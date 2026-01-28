//! Lexer of Muon.

use std::{mem, sync::Arc};

use muonc_errors::prelude::*;
use muonc_middle::session::Session;
use muonc_span::{
    FileId, Span, span,
    symbol::{Symbol, sym},
};
use muonc_token::{Keyword, Lit, Token, TokenStream, TokenType};

use crate::diags::{
    EmptyCharLiteral, ExpectedExponentPart, InvalidDigitInNumber, InvalidUnicodeEscape,
    InvalidUnicodeNote, NoDigitsInANonDecimal, NotEnoughHexDigits, ReachedEof,
    TooLargeIntegerLiteral, TooManyCodepointsInCharLiteral, UnknownCharacterEscape, UnknownToken,
    UnterminatedBlockComment, UnterminatedStringLiteral,
};

pub mod diags;

/// Configuration options for integer parsing.
///
/// This struct is used to customize how parsing diagnostics are reported,
/// particularly where the input string began in the source, and more.
///
/// # Fields
///
/// * `base_bytes`
///   The byte offset of the start of the number in the source input. Used for
///   generating accurate error spans.
#[derive(Debug, Clone)]
pub struct IntegerLexOptions {
    /// the base position where the parsing of the integer starts
    base_bytes: usize,
    /// span of the integer that is currently being parsed
    int_span: Option<Span>,
    /// do we emit diagnostic while parsing the number?
    ///
    /// # Note
    ///
    /// This is useful when we need to parse a number but we already emit a
    /// custom error when an error is occurring
    emit_diags: bool,
}

/// Lexing cursor.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Cursor {
    bytes: usize,
    chars: usize,
}

impl Cursor {
    /// Create a zeroed cursor
    pub fn new() -> Cursor {
        Cursor { bytes: 0, chars: 0 }
    }

    /// Increments the cursor according to the first byte of the following
    /// character.
    pub fn increment(&mut self, c: char) {
        self.chars += 1;
        self.bytes += c.len_utf8();
    }

    /// Offset in bytes since the start.
    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// Takes the byte offset of the cursor and adds `offset` and returns it.
    pub fn bytes_with(&self, offset: isize) -> usize {
        (self.bytes as isize + offset) as usize
    }

    /// The offset in amount of UTF-8 characters since the start.
    pub fn chars(&self) -> usize {
        self.chars
    }
}

/// Lexer -- turns source code into a stream of tokens.
#[derive(Debug, Clone)]
pub struct Lexer<'source> {
    /// The starting positon of the current token
    prev: Cursor,
    /// The current position where the lexer is working
    cur: Cursor,
    /// Diagnostic context.
    dcx: DiagCtxt,
    /// The src represented as a vector of chars, a UTF-32 kinda version of it.
    chars: Vec<char>,
    /// The source file.
    src: &'source str,
    /// The file id of the file with are lexing.
    fid: FileId,
}

impl<'source> Lexer<'source> {
    /// Create a new lexer with the given session and file id.
    ///
    /// NB: `src` must correspond to the source code of the file at `fid`.
    pub fn new(src: &'source str, session: Arc<Session>, fid: FileId) -> Lexer<'source> {
        #[cfg(debug_assertions)]
        {
            assert!(
                session.sm.exists(fid),
                "the file id doesn't exist in the source map"
            );
            assert_eq!(
                src,
                session.sm.ref_src(fid),
                "the source and the file id aren't matching"
            );
        }

        Lexer {
            prev: Cursor::new(),
            cur: Cursor::new(),
            dcx: session.dcx.clone(),
            chars: src.chars().collect(),
            src,
            fid,
        }
    }

    /// Returns the span between the previous and the current cursors.
    pub fn span(&self) -> Span {
        Span {
            lo: self.prev.bytes(),
            hi: self.cur.bytes(),
            fid: self.fid,
        }
    }

    /// Returns the span of the current character.
    pub fn span_current_char(&self) -> Span {
        let cur = self.cur.bytes();
        let width = self.current().expect("expected a character").len_utf8();

        span(cur, cur + width, self.fid)
    }

    /// Returns the current character.
    #[inline]
    #[must_use = "looking at the current char is a no-op if you don't use the result"]
    pub fn current(&self) -> Option<char> {
        self.ahead(0)
    }

    /// Returns the `dist` characters ahead of the current position.
    #[inline]
    #[must_use = "looking ahead is a no-op if you don't use the result"]
    pub fn ahead(&self, dist: isize) -> Option<char> {
        self.chars.get(self.cur.bytes_with(dist)).copied()
    }

    /// Eats the current character and returns it.
    pub fn eat(&mut self) -> Option<char> {
        let c = self.current();

        self.cur.increment(c.unwrap_or_default());

        c
    }

    /// Eats until we reach the `stoper` character but we do not eat it.
    pub fn eat_until(&mut self, stopper: char) -> &str {
        let start = self.cur.bytes();

        loop {
            match self.current() {
                Some(c) if c == stopper => break,
                Some(_) => {
                    self.eat();
                }
                None => break,
            }
        }

        &self.src[start..self.cur.bytes()]
    }

    /// Eats the current character and assert (in debug mode only) that it is the expected one.
    #[track_caller]
    pub fn eat_assert(&mut self, expected: char) -> char {
        let eaten = self.eat();

        match eaten {
            Some(eaten) if eaten == expected => eaten,
            Some(_) => panic!("expected {expected:?} but got {eaten:?}."),
            None => panic!("expected a token but reached the end of file."),
        }
    }

    /// Eats something that is an alphanumerical sequence of characters without
    /// whitespaces and returns a string to it.
    pub fn eat_word(&mut self) -> &'source str {
        let start = self.cur.bytes();

        while let Some(c @ ('A'..='Z' | 'a'..='z' | '_' | '0'..='9')) = self.current() {
            self.eat_assert(c);
        }

        let end = self.cur.bytes();

        &self.src[start..end]
    }

    /// Like `eat_word` but returns a Symbol.
    pub fn eat_symbol(&mut self) -> Symbol {
        Symbol::intern(self.eat_word())
    }

    /// Lex the all source code and returns a **finished** token stream.
    pub fn produce(&mut self) -> ReResult<TokenStream> {
        let mut ts = TokenStream::new();

        // an indicator if whetever we have failed but did recovered.
        let mut tainted_by_errors: Option<DiagGuaranteed> = None;

        loop {
            // replace the previous position by the current one of the last loop
            _ = mem::replace(&mut self.prev, self.cur.clone());

            let tt = match self.lex_one() {
                Ok(t) => t,
                Err(Recovered::Yes(t, guarantee)) => {
                    tainted_by_errors = Some(guarantee);

                    t
                }
                Err(Recovered::No(guarantee)) => return Err(Recovered::No(guarantee)),
            };

            if tt == TokenType::Dummy {
                // don't add dummy tokens to a token stream.
                continue;
            }

            if ts.push(Token {
                tt,
                span: self.span(),
            }) {
                // reached Eof.
                break;
            }
        }

        ts.finish();

        if let Some(guarantee) = tainted_by_errors {
            Err(Recovered::Yes(ts, guarantee))
        } else {
            Ok(ts)
        }
    }

    /// Lex a token and return it.
    pub fn lex_one(&mut self) -> ReResult<TokenType> {
        use TokenType::*;

        let tt = match self.current() {
            Some('(') => LParen,
            Some(')') => RParen,
            Some('[') => LBracket,
            Some(']') => RBracket,
            Some('{') => LCurly,
            Some('}') => RCurly,
            Some('+') => Plus,
            Some('-') => {
                self.eat();
                match self.current() {
                    Some('>') => {
                        self.eat();
                        return Ok(MinusGt);
                    }
                    _ => return Ok(Minus),
                }
            }
            Some('*') => Star,
            Some(':') => {
                self.eat();

                match self.current() {
                    Some(':') => {
                        self.eat();
                        return Ok(ColonColon);
                    }
                    _ => return Ok(Colon),
                }
            }
            Some(',') => Comma,
            Some(';') => Semi,
            Some('^') => Caret,
            Some('&') => {
                self.eat();

                match self.current() {
                    Some('&') => {
                        self.eat();
                        return Ok(AndAnd);
                    }
                    _ => return Ok(And),
                }
            }
            Some('|') => {
                self.eat();

                match self.current() {
                    Some('|') => {
                        self.eat();
                        return Ok(OrOr);
                    }
                    _ => return Ok(Or),
                }
            }
            Some('%') => Percent,
            Some('#') => Pound,
            Some('=') => {
                self.eat();

                match self.current() {
                    Some('=') => {
                        self.eat();
                        return Ok(EqEq);
                    }
                    _ => return Ok(Eq),
                }
            }
            Some('!') => {
                self.eat();

                return match self.current() {
                    Some('=') => {
                        self.eat();
                        Ok(BangEq)
                    }
                    _ => Ok(Bang),
                };
            }
            Some('<') => {
                self.eat();
                match self.current() {
                    Some('=') => {
                        self.eat();
                        return Ok(LtEq);
                    }
                    Some('<') => {
                        self.eat();
                        return Ok(LtLt);
                    }
                    _ => return Ok(Lt),
                }
            }
            Some('>') => {
                self.eat();
                match self.current() {
                    Some('=') => {
                        self.eat();
                        return Ok(GtEq);
                    }
                    Some('>') => {
                        self.eat();
                        return Ok(GtGt);
                    }
                    _ => return Ok(Gt),
                }
            }
            Some('/') => {
                self.eat();
                match self.current() {
                    Some('/') => {
                        // start of a line comment
                        self.eat();
                        self.eat_until('\n');
                        return Ok(TokenType::Dummy);
                    }
                    Some('*') => {
                        // start of multiline comment
                        self.eat();

                        loop {
                            match (self.current(), self.ahead(1)) {
                                (Some('*'), Some('/')) => break,
                                (Some(_), _) => {
                                    self.eat();
                                }
                                (None, _) => {
                                    return self
                                        .dcx
                                        .emit(UnterminatedBlockComment {
                                            primary: self.span(),
                                        })
                                        .recover();
                                }
                            }
                        }

                        self.eat(); // eat *
                        self.eat(); // eat /

                        return Ok(TokenType::Dummy);
                    }
                    _ => return Ok(Slash),
                }
            }
            Some('.') => {
                self.eat();
                match self.current() {
                    Some('*') => {
                        self.eat();
                        return Ok(DotStar);
                    }
                    _ => return Ok(Dot),
                }
            }
            Some('\'') => return self.lex_char(),
            Some('"') => return self.lex_string().re_map(TokenType::Lit),
            Some('a'..='z' | 'A'..='Z' | '_') => return self.lex_identifier(),
            Some('0'..='9') => return self.lex_number().re_map(TokenType::Lit),
            Some(w) if w.is_whitespace() => {
                self.eat(); // eat the whitespace
                return Ok(TokenType::Dummy);
            }
            Some(c) => {
                self.eat();

                return self
                    .dcx
                    .emit(UnknownToken {
                        c,
                        primary: self.span(),
                    })
                    .recover();
            }
            None => Eof,
        };

        self.eat();

        Ok(tt)
    }

    /// Lexes something that starts and looks like an identifier.
    pub fn lex_identifier(&mut self) -> ReResult<TokenType> {
        let word = self.eat_symbol();

        match self.current() {
            Some('\"') => {
                let mut lit = match self.lex_string_with(false) {
                    Ok(lit) | Err(Recovered::Yes(lit, _)) => lit,
                    Err(_) => Lit::string(sym::empty),
                };

                lit.tag = Some(word);

                Ok(TokenType::Lit(lit))
            }
            Some('\'') => {
                let mut lit = match self.lex_char() {
                    Ok(TokenType::Lit(lit)) | Err(Recovered::Yes(TokenType::Lit(lit), _)) => lit,
                    Ok(_) => unreachable!(),
                    Err(_) => Lit::char(char::default()),
                };

                lit.tag = Some(word);

                Ok(TokenType::Lit(lit))
            }
            _ => {
                if let Some(kw) = Keyword::from_symbol(word) {
                    Ok(TokenType::Kw(kw))
                } else {
                    Ok(TokenType::Ident(word))
                }
            }
        }
    }

    /// Lexes tokens that look like numbers: integers and floats.
    pub fn lex_number(&mut self) -> ReResult<Lit> {
        let mut number = tri!(self.lex_number_internal(), default: Lit::int(0));

        match self.current() {
            Some('\'') => {
                self.eat(); // eat '

                let tag = self.eat_symbol();

                number.tag = Some(tag);
            }
            _ => {}
        }

        Ok(number)
    }

    /// Internal function used by `lex_number` it's the same it just doesn't support tags.
    fn lex_number_internal(&mut self) -> ReResult<Lit> {
        // Integer literal grammar:
        //
        // int_lit         = decimal_lit | binary_lit | octal_lit | hex_lit ;
        // decimal_lit     = "0" | decimal_digits ;
        // binary_lit      = ("0b" | "0B") binary_digits ;
        // octal_lit       = ("0o" | "0O") octal_digits ;
        // hex_lit         = ("0x" | "0X") hex_digits ;
        //
        // decimal_digits  = decimal_digit ( "_" decimal_digit )* ;
        // binary_digits   = binary_digit  ( "_" binary_digit  )* ;
        // octal_digits    = octal_digit   ( "_" octal_digit   )* ;
        // hex_digits      = hex_digit     ( "_" hex_digit     )* ;

        let radix = match self.ahead(1) {
            Some('B' | 'b') if self.current() == Some('0') => {
                self.eat(); // eat 0
                self.eat(); // eat B / b
                2
            }
            Some('O' | 'o') if self.current() == Some('0') => {
                self.eat(); // eat 0
                self.eat(); // eat O / o
                8
            }
            Some('X' | 'x') if self.current() == Some('0') => {
                // Hex float literal grammar:
                //
                // hex_float_lit        = ("0x" | "0X") hex_mantissa hex_exponent ;
                // hex_mantissa =
                //       hex_digits "." [ hex_digits ]
                //     | hex_digits
                //     | "." hex_digits ;
                // hex_exponent         = ("p" | "P") ["+" | "-"] decimal_digits ;

                self.eat(); // eat 0
                self.eat(); // eat X / x
                let int_str = self.eat_word();
                let int_part = tri!(self.parse_u128(&int_str, 16), default: 0);

                match self.current() {
                    Some('.') => {
                        self.eat(); // eat .

                        let frac_str = self.eat_word();
                        let (frac_part, frac_divisor) =
                            match self.parse_u128_with_digit_count(&frac_str, 16) {
                                Ok((f, n)) => (f, n as i32),
                                Err(_) => (0, 0),
                            };

                        let exp_value = match self.current() {
                            Some('p' | 'P') => {
                                self.eat(); // eat p / P

                                let sign = match self.current() {
                                    Some('-') => {
                                        self.eat(); // eat -
                                        -1i32
                                    }
                                    Some('+') => {
                                        self.eat(); // eat +
                                        1i32
                                    }
                                    Some('_' | '0'..='9') => 1i32,
                                    Some(c) => {
                                        self.dcx.emit(InvalidDigitInNumber {
                                            c,
                                            primary: self.span_current_char(),
                                            int_span: self.span(),
                                        });
                                        1i32
                                    }
                                    _ => {
                                        self.dcx.emit(ReachedEof {
                                            primary: self.span(),
                                        });
                                        1i32
                                    }
                                };

                                let exp_str = self.eat_word();

                                let exp = match self.parse_u128(&exp_str, 10) {
                                    Ok(e) => e as i32,
                                    Err(_) => 0,
                                };

                                sign * exp
                            }
                            Some(found) => {
                                self.dcx.emit(ExpectedExponentPart {
                                    found,
                                    primary: self.span_current_char(),
                                    float_span: self.span(),
                                });

                                0
                            }
                            None => {
                                self.dcx.emit(ReachedEof {
                                    primary: self.span(),
                                });

                                0
                            }
                        };

                        let int_f64 = int_part as f64;
                        let frac_f64 = frac_part as f64 * 16f64.powi(-frac_divisor);

                        let base = int_f64 + frac_f64;

                        let float = base * 2.0f64.powi(exp_value);

                        return Ok(Lit::float(float));
                    }
                    Some('p' | 'P') => {
                        self.eat(); // eat p / P
                        let sign = match self.current() {
                            Some('-') => {
                                self.eat(); // eat -
                                -1i32
                            }
                            Some('+') => {
                                self.eat(); // eat +
                                1i32
                            }

                            Some('_' | '0'..='9') => 1,
                            Some(c) => {
                                self.dcx.emit(InvalidDigitInNumber {
                                    c,
                                    primary: self.span_current_char(),
                                    int_span: self.span(),
                                });

                                1
                            }
                            _ => {
                                self.dcx.emit(ReachedEof {
                                    primary: self.span(),
                                });

                                1
                            }
                        };

                        let exp_str = self.eat_word();

                        let exp_value = sign
                            * match self.parse_u128(&exp_str, 10) {
                                Ok(e) => e as i32,
                                Err(_) => 0,
                            };

                        let int_f64 = int_part as f64;
                        let float = int_f64 * 2.0f64.powi(exp_value);

                        return Ok(Lit::float(float));
                    }
                    _ => {
                        if int_str.is_empty() {
                            self.dcx.emit(NoDigitsInANonDecimal {
                                primary: self.span(),
                            });
                        }
                        return Ok(Lit::int(int_part));
                    }
                }
            }
            _ => 10,
        };
        let int_str = self.eat_word();

        if int_str.is_empty() {
            self.dcx.emit(NoDigitsInANonDecimal {
                primary: self.span(),
            });
        }

        let int_part = tri!(self.parse_u128(&int_str, radix), default: 0);

        match self.current() {
            Some('.') if radix == 10 => {
                // Decimal float lit grammar:
                //
                // float_lit            = decimal_float_lit | hex_float_lit ;
                // decimal_float_lit    =
                //       decimal_digits "." [ decimal_digits ] [ decimal_exponent ]
                //     | decimal_digits decimal_exponent
                //     | "." decimal_digits [ decimal_exponent ] ;
                // decimal_exponent     = ("e" | "E") ["+" | "-"] decimal_digits ;

                self.eat(); // eat .

                let frac_str = self.eat_word();
                let (frac_part, frac_divisor) =
                    match self.parse_u128_with_digit_count(&frac_str, 10) {
                        Ok((f, n)) => (f, n as i32),
                        Err(_) => (0, 0),
                    };

                let exp_value = match self.current() {
                    Some('e' | 'E') => {
                        self.eat(); // eat e / E

                        let sign = match self.current() {
                            Some('-') => {
                                self.eat(); // eat -

                                -1i32
                            }
                            Some('+') => {
                                self.eat(); // eat +
                                1
                            }
                            Some('_' | '0'..='9') => 1,
                            Some(c) => {
                                self.dcx.emit(InvalidDigitInNumber {
                                    c,
                                    primary: self.span_current_char(),
                                    int_span: self.span(),
                                });
                                1
                            }
                            _ => {
                                self.dcx.emit(ReachedEof {
                                    primary: self.span(),
                                });
                                1
                            }
                        };

                        let exp_str = self.eat_word();

                        let exp = tri!(self.parse_u128(&exp_str, 10), default: 0) as i32;

                        sign * exp
                    }
                    _ => 0,
                };

                let int_f64 = int_part as f64;
                let frac_f64 = frac_part as f64 * 10f64.powi(-frac_divisor);

                let base = int_f64 + frac_f64;

                let float = base * 10.0f64.powi(exp_value);

                Ok(Lit::float(float))
            }
            _ => Ok(Lit::int(int_part)),
        }
    }

    /// Lexes a string with support for escape sequences
    pub fn lex_string(&mut self) -> ReResult<Lit> {
        self.lex_string_with(true)
    }

    /// Lexes string with a support for escape sequence if `escape` is true.
    pub fn lex_string_with(&mut self, escape: bool) -> ReResult<Lit> {
        // NB.: here we cannot really use the technique like for identifiers
        // like we take a slice of the source code and turn it into a symbol,
        // because it would only work if `escape` is false or if the string
        // doesn't contains escape sequences. it scould be added in the future
        // but for now we build the resulting string literal character by
        // character.

        let mut str = String::new();
        // eat the first double quote
        self.eat_assert('"');

        loop {
            match self.current() {
                Some('"') => {
                    // eat the last double quote
                    self.eat();

                    break;
                }
                Some('\\') if escape => {
                    self.eat();

                    let es = match self.eat() {
                        Some(es) => es,
                        None => continue,
                    };

                    if es == '"' {
                        str.push(es);
                        continue;
                    }

                    if let Ok(c) = self.lex_escape_sequence(es, true) {
                        str.push(c);
                    }
                }
                Some(c) => {
                    str.push(c);
                    self.eat();
                }
                _ => {
                    self.dcx.emit(UnterminatedStringLiteral {
                        primary: self.span(),
                    });
                    break;
                }
            }
        }

        Ok(Lit::string(Symbol::intern(&str)))
    }

    /// Lexex a character literal.
    pub fn lex_char(&mut self) -> ReResult<TokenType> {
        self.eat_assert('\'');

        let mut empty_char = false;
        let c = match self.current() {
            Some('\\') => {
                self.eat();

                let es = match self.eat() {
                    Some(es) => es,
                    None => {
                        self.dcx.emit(ReachedEof {
                            primary: self.span(),
                        });
                        char::default()
                    }
                };

                if es == '\'' {
                    es
                } else {
                    tri!(self.lex_escape_sequence(es, false))
                }
            }
            Some('\'') => {
                self.eat();
                self.dcx.emit(EmptyCharLiteral {
                    primary: self.span(),
                });
                empty_char = true;
                char::default()
            }
            Some(c) => {
                self.eat();
                c
            }
            None => {
                self.dcx.emit(ReachedEof {
                    primary: self.span(),
                });
                char::default()
            }
        };

        if !empty_char {
            match self.current() {
                Some('\'') => {
                    self.eat();
                }
                Some(_) => {
                    self.eat_until('\'');
                    self.eat_assert('\'');
                    self.dcx.emit(TooManyCodepointsInCharLiteral {
                        primary: self.span(),
                    });
                }
                None => {
                    self.dcx.emit(ReachedEof {
                        primary: self.span(),
                    });
                }
            }
        }

        Ok(TokenType::Lit(Lit::char(c)))
    }

    /// makes an escape sequence return a tuple of the character that corresponds
    /// to the escape and the increments to make to the head
    pub fn lex_escape_sequence(&mut self, es: char, string: bool) -> ReResult<char> {
        #[inline(always)]
        fn char(i: u8) -> char {
            i as char
        }

        let es = match es {
            '0' => char(0x00),
            'n' => char(0x0A),
            'r' => char(0x0D),
            'f' => char(0x0C),
            't' => char(0x09),
            'v' => char(0x0B),
            'a' => char(0x07),
            'b' => char(0x08),
            'e' => char(0x1B),
            '\\' => char(0x5C), // \
            'x' => self.lex_hex_escape(string)?,
            'u' => {
                match self.current() {
                    Some('{') => {
                        self.eat();
                    }
                    _ => {
                        self.dcx.emit(InvalidUnicodeEscape {
                            note: InvalidUnicodeNote::ExpectedOpeningBrace,
                            primary: self.span_current_char(),
                        });
                    }
                }
                let old_cur = self.cur.bytes();
                let hex_str = self.eat_word().to_string();

                if hex_str.is_empty() {
                    self.dcx.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::EmptyUnicode,
                        primary: self.span_current_char(),
                    });
                }

                let hex: u32 = match tri!(self.parse_u128_with_options(
                    &hex_str,
                    16,
                    IntegerLexOptions {
                        base_bytes: old_cur,
                        int_span: Some(span(old_cur, self.cur.bytes(), self.fid)),
                        emit_diags: false,
                    },
                ))
                .try_into()
                {
                    Ok(h) => h,
                    Err(_) => {
                        // NB: because of the `tri!` we can't have a `Err(Recovered::Yes(..))`.
                        self.dcx.emit(InvalidUnicodeEscape {
                            note: InvalidUnicodeNote::TooBig,
                            primary: self.span(),
                        });

                        0x00
                    }
                };

                match self.current() {
                    Some('}') => {
                        self.eat();
                    }
                    _ => {
                        self.dcx.emit(InvalidUnicodeEscape {
                            note: InvalidUnicodeNote::ExpectedClosingBrace,
                            primary: self.span_current_char(),
                        });
                    }
                }

                if let Some(c) = char::from_u32(hex) {
                    c
                } else {
                    self.dcx.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::MustNotBeASurrogate,
                        primary: self.span(),
                    });

                    char::default()
                }
            }
            _ => {
                self.dcx.emit(UnknownCharacterEscape {
                    es,
                    primary: span(self.cur.bytes() - 1, self.cur.bytes(), self.fid),
                    // TODO: fix the location of the literal, this is wrong.
                    lit_span: self.span(),
                });

                char::default()
            }
        };

        Ok(es)
    }

    /// set string to true if the escape sequence is part of a string, false if
    /// it is part of a char literal
    pub fn lex_hex_escape(&mut self, string: bool) -> ReResult<char> {
        let mut str = String::with_capacity(2);
        for _ in 0..2 {
            str.push(match self.current() {
                Some('\'') if !string => {
                    self.dcx.emit(NotEnoughHexDigits {
                        primary: span(self.prev.bytes(), self.cur.bytes() + 1, self.fid),
                    });
                    break;
                }
                Some('"') if string => {
                    self.dcx.emit(NotEnoughHexDigits {
                        primary: span(self.prev.bytes(), self.cur.bytes() + 1, self.fid),
                    });
                    break;
                }
                Some(_) => self.eat().unwrap(),
                None => {
                    self.eat();
                    self.dcx.emit(UnterminatedStringLiteral {
                        primary: self.span(),
                    });
                    // it's the poisoned value.
                    str.push_str("00");
                    break;
                }
            })
        }

        let cur_bytes = self.cur.bytes();

        Ok(tri!(self.parse_u128_with_options(
            &str,
            16,
            IntegerLexOptions {
                base_bytes: cur_bytes - 2,
                int_span: { Some(span(cur_bytes - 2, cur_bytes, self.fid)) },
                emit_diags: true,
            },
        )) as u8 as char)
    }

    /// Low-level parser for a `u128` with full error reporting and
    /// customization.
    ///
    /// This function gives the most control over parsing, including byte
    /// offset for accurate diagnostics. It reports invalid digits and handles
    /// underscores as digit separators (like Rust's numeric syntax).
    ///
    /// # Arguments
    ///
    /// * `input` - The string to parse.
    /// * `radix` - The numeric base (2–36 inclusive).
    /// * `options` - Parsing options (e.g. base offset for spans).
    ///
    /// # Returns
    ///
    /// Returns a tuple `(value, digit_count)`:
    /// * `value` - The parsed `u128` integer.
    /// * `digit_count` - Number of valid digits parsed (excluding underscores).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is not between 2 and 36.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if an invalid character is encountered or the
    /// value overflows.
    ///
    /// [`Diagnostic`]: lunc_diag::Diagnostic
    pub fn parse_u128_advanced(
        &mut self,
        input: &str,
        radix: u8,
        options: IntegerLexOptions,
    ) -> ReResult<(u128, u32)> {
        if !(2..=36).contains(&radix) {
            panic!("invalid radix provided, {radix}, it must be between 2 and 36 included.")
        }

        let mut result: u128 = 0;
        // did the literal is too big too fit in a u128
        let mut overflowed = false;
        // don't emit the integer too large if there was an overflow, deal one
        // thing at a time
        let mut errored = false;

        // count of how many digits of the radix we parsed
        let mut digit_count = 0;

        for (i, c) in input.char_indices().peekable() {
            let digit = match c {
                '0'..='9' => (c as u8 - b'0') as u32,
                'a'..='z' => (c as u8 - b'a' + 10) as u32,
                'A'..='Z' => (c as u8 - b'A' + 10) as u32,
                '_' => continue,
                _ => {
                    errored = true;
                    let pos = options.base_bytes + i;
                    if options.emit_diags {
                        self.dcx.emit(InvalidDigitInNumber {
                            c,
                            primary: span(pos, pos + 1, self.fid),
                            int_span: options.int_span.unwrap_or_else(|| self.span()),
                        });
                    }

                    // the poisoned value
                    0
                }
            };

            if digit >= radix.into() {
                errored = true;
                let pos = options.base_bytes + i;
                self.dcx.emit(InvalidDigitInNumber {
                    c,
                    primary: span(pos, pos + 1, self.fid),
                    int_span: options.int_span.unwrap_or_else(|| self.span()),
                });
            } else {
                digit_count += 1
            }

            let prev_result = result;
            result = match result
                .checked_mul(radix as u128)
                .and_then(|r| r.checked_add(digit as u128))
            {
                Some(val) => val,
                None => {
                    overflowed = true;
                    prev_result
                }
            };
        }

        if overflowed && !errored && options.emit_diags {
            self.dcx.emit(TooLargeIntegerLiteral {
                primary: self.span(),
            });
        }

        if errored {
            // we can't trust the output of this function if one of the digit
            // wasn't one the radix could handle.
            if self.dcx.failed() {
                self.dcx
                    .has_emitted()
                    .expect("the dcx failed but it didn't emit ?!")
                    .recover()
            } else {
                // can't have a DiagGuaranteed probably because
                // options.emit_diags is false.
                Ok((0, digit_count))
            }
        } else {
            Ok((result, digit_count))
        }
    }

    /// Parse a string slice into a `u128` integer using the specified radix.
    ///
    /// This function is a convenience wrapper that parses the input string and
    /// returns only the parsed integer. If the input is malformed or the number
    /// is too large, a diagnostic error is returned.
    ///
    /// # Note
    ///
    /// The radix is 'inclusive' if you want to parse a number as a decimal,
    /// then `radix = 10` and if you want to parse a number as hexadecimal
    /// `radix = 16` etc etc...
    ///
    /// # Arguments
    ///
    /// * `input` - The string slice to parse.
    /// * `radix` - The base to use (between 2 and 36).
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if the input is invalid or too large.
    ///
    /// [`Diagnostic`]: lunc_diag::Diagnostic
    pub fn parse_u128(&mut self, input: &str, radix: u8) -> ReResult<u128> {
        self.parse_u128_with_digit_count(input, radix)
            .re_map(|(int, _)| int)
    }

    /// Parse a string slice into a `u128` integer using the specified radix and
    /// custom options.
    ///
    /// Allows fine-grained control over how the number is parsed by passing
    /// additional options like the base byte offset for error location
    /// reporting.
    ///
    /// # Arguments
    ///
    /// * `input` - The string slice to parse.
    /// * `radix` - The base to use (between 2 and 36).
    /// * `options` - Parsing configuration such as base byte offset.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] on overflow or invalid input.
    ///
    /// [`Diagnostic`]: lunc_diag::Diagnostic
    pub fn parse_u128_with_options(
        &mut self,
        input: &str,
        radix: u8,
        options: IntegerLexOptions,
    ) -> ReResult<u128> {
        self.parse_u128_advanced(input, radix, options)
            .re_map(|(int, _)| int)
    }

    /// Parse a string slice into a `u128` and return how many digits were
    /// parsed.
    ///
    /// This is useful when you need to know how many characters in the input
    /// were part of a valid number. It uses the specified radix.
    ///
    /// # Arguments
    ///
    /// * `input` - The string to parse.
    /// * `radix` - The numeric base (between 2 and 36).
    ///
    /// # Returns
    ///
    /// Returns a tuple `(value, digit_count)`:
    /// * `value` - The parsed `u128` integer.
    /// * `digit_count` - The number of valid digits parsed.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if the input is invalid or overflows.
    ///
    /// [`Diagnostic`]: lunc_diag::Diagnostic
    pub fn parse_u128_with_digit_count(&mut self, input: &str, radix: u8) -> ReResult<(u128, u32)> {
        self.parse_u128_advanced(
            input,
            radix,
            IntegerLexOptions {
                base_bytes: self.prev.bytes(),
                int_span: None,
                emit_diags: true,
            },
        )
    }
}
