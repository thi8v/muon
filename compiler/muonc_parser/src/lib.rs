//! Parser of Muon.

use std::{borrow::Cow, mem};

use bitflags::bitflags;
use muonc_errors::prelude::*;
use muonc_span::prelude::*;
use muonc_token::{
    ExpToken, ExpTokenSet, Keyword, Lit, Token, TokenStream,
    TokenType::{self, *},
    TsSealed, WeakKw,
};

use muonc_middle::ast::*;

use crate::diags::ExpectedToken;
use ast::*;

pub mod ast;
pub mod diags;
pub mod directive;
pub mod expr;
pub mod item;
pub mod pretty;
pub mod stmt;
pub mod typ;

/// A parsing function.
pub type ParsingFn<T> = fn(&mut Parser) -> ReResult<T>;

/// Parser of Muon, turns the tokens into an Abstract Syntax Tree.
#[derive(Debug)]
pub struct Parser {
    /// token stream, ensured to be finished.
    pub(crate) tokens: TokenStream<TsSealed>,
    /// token index
    pub(crate) ti: usize,
    /// diagnostic context
    pub(crate) dcx: DiagCtxt,
    /// file id of the file being parsed
    pub(crate) fid: FileId,
    /// The current token
    pub(crate) token: Token,
    /// The previous token
    pub(crate) prev_token: Token,
    /// The expected token reprs.
    pub(crate) expected_token_exps: ExpTokenSet,
    /// The recovery status of the parser, if set to `true`, there parser can be
    /// more keen about errors.
    pub(crate) recovery: bool,
    /// Restrictions on the parsing, and on what the diagnostics will look like.
    pub(crate) restrictions: Restrictions,
    /// Used by [`Parser::parse_expr_stmt`].
    pub(crate) expr_semi_diag: Option<ExpectedToken>,
}

impl Parser {
    /// Create a new parser.
    pub fn new(tokens: TokenStream<TsSealed>, dcx: DiagCtxt, fid: FileId) -> Parser {
        let token = tokens.get(0).clone();

        Parser {
            tokens,
            ti: 0,
            dcx,
            fid,
            token,
            prev_token: Token::dummy(),
            expected_token_exps: ExpTokenSet::new(),
            recovery: false,
            restrictions: Restrictions::empty(),
            expr_semi_diag: None,
        }
    }

    /// Advances the parser by one token.
    pub fn bump(&mut self) {
        // get the next token
        self.ti += 1;
        let next = self.tokens.get(self.ti).clone();

        // update the current and previous token
        self.prev_token = mem::replace(&mut self.token, next);

        // diagnostic.
        self.expected_token_exps.clear();
    }

    /// Checks if the next token is `exp.tok`, if so returns `true`.
    ///
    /// This method add `exp` to the `Parser::expected_token_exps` set if `exp`
    /// is not encountered.
    pub fn check(&mut self, exp: ExpToken) -> bool {
        let is_present = self.token.tt == exp;

        if !is_present {
            self.expected_token_exps.insert(exp);
        }

        is_present
    }

    /// [`Parser::check`] but do not add `exp` to `Parser::expected_token_exps`.
    #[inline(always)]
    pub fn check_no_expect(&self, exp: ExpToken) -> bool {
        self.token.tt == exp
    }

    /// Consumes the `exp.tok` if it exists. Returns `true` if it existed or
    /// `false` if it did not.
    pub fn eat(&mut self, exp: ExpToken) -> bool {
        let is_present = self.check(exp);

        if is_present {
            self.bump();
        }

        is_present
    }

    /// Consumes one of the `edible` if it exists, and return true, or check if
    /// it's in `inedible` and return true. In other cases return false.
    ///
    /// # Note
    ///
    /// This function adds neither `exp`s from `edible` or `inedible` into
    /// `Parser::expected_token_exps`
    pub fn eat_one_of(
        &mut self,
        edible: impl IntoIterator<Item = ExpToken>,
        inedible: impl IntoIterator<Item = ExpToken>,
    ) -> bool {
        if edible.into_iter().any(|exp| self.check_no_expect(exp)) {
            self.bump();
            true
        } else {
            inedible.into_iter().any(|exp| self.check_no_expect(exp))
        }
    }

    /// [`Parser::eat`] but do not add `exp` to `Parser::expected_token_exps`.
    pub fn eat_no_expect(&mut self, exp: ExpToken) -> bool {
        let is_present = self.check_no_expect(exp);

        if is_present {
            self.bump();
        }

        is_present
    }

    /// Consumes the next token if it is a [`TokenType::Lit`]. Returns
    /// `Some(lit)` if it existed or `None` if it did not.
    pub fn eat_lit(&mut self) -> Option<Lit> {
        match &self.token.tt {
            TokenType::Lit(lit) => {
                let lit = lit.clone();
                self.bump();

                Some(lit)
            }
            _ => None,
        }
    }

    /// Expects and consumes the token `exp`, or something else if it's not
    /// `exp`. Signals an error if the next token isn't `exp`. Returns the span
    /// of the consumed token if it was the correct one.
    #[track_caller]
    #[inline(never)]
    pub fn expect(&mut self, exp: ExpToken) -> ReResult<Span> {
        tri!(self._expect_advance(exp, true));
        Ok(self.token_span())
    }

    /// Expect and consumes the token `exp`, it may also break in two the
    /// `Parser::token` but only if the first half of the breoken token is
    /// `exp`. Signals an error if the next token isn't `exp` and it's broken
    /// first half isn't `exp`. Returns the span of the consumed token if it was
    /// the correct one.
    pub fn expect_and_break(&mut self, exp: ExpToken) -> ReResult<Span> {
        if self.eat_no_expect(exp) {
            Ok(self.token_span())
        } else if let Some(broken_t) = self.token.break_up()
            && broken_t[0].tt == exp
        {
            // replace the broken parts in token stream and as current token
            self.tokens.replace_with_two(self.ti, broken_t.clone());
            self.token = broken_t[0].clone();

            // eat the first half of the token
            self.bump();

            Ok(self.token_span())
        } else {
            // token was not not present
            self.expected_token_exps.insert(exp);

            let diag = self.expected_diag();
            self.bump();

            Err(Recovered::No(self.dcx.emit(diag)))
        }
    }

    /// Expects and consumes the token `exp` if it exists. Signals an error if
    /// the next token isn't `exp`.
    ///
    /// *`expect_nae` for `EXPECT Not Always Eat`*
    #[track_caller]
    #[inline(never)]
    pub fn expect_nae(&mut self, exp: ExpToken) -> ReResult<()> {
        self._expect_advance(exp, false)
    }

    #[track_caller]
    #[inline(always)]
    fn _expect_advance(&mut self, exp: ExpToken, eat_unexpected: bool) -> ReResult<()> {
        if !self.eat(exp) {
            // token was not present
            let diag = self.expected_diag();

            if eat_unexpected {
                self.bump();
            }

            return Err(Recovered::No(self.dcx.emit(diag)));
        }

        Ok(())
    }

    /// Expects and consumes a weak keyword. Signals an error if the token isn't
    /// `weak_kw`. Returns the span of the weak kw, or a dummy span if it wasn't
    /// the weak kw.
    pub fn expect_weak_kw(&mut self, weak_kw: WeakKw) -> ReResult<Span> {
        if !self.eat_no_expect(ExpToken::Ident) {
            return Err(Recovered::No({
                self.dcx.emit(ExpectedToken::new(
                    [format!("weak keyword `{}`", weak_kw.as_symbol())],
                    self.token.clone(),
                ))
            }));
        }

        let id = self.as_ident();
        if id.name != weak_kw.as_symbol() {
            return Err(Recovered::No({
                self.dcx.emit(ExpectedToken::new(
                    [format!("weak keyword `{}`", weak_kw.as_symbol())],
                    self.token.clone(),
                ))
            }));
        }

        Ok(self.token_span())
    }

    /// Create a new expected diag with the current token and the
    /// `Parser::expected_token_exps`.
    ///
    /// # Note
    ///
    /// This function also resets the `Parser::expected_token_exps`.
    pub fn expected_diag(&mut self) -> ExpectedToken {
        let mut res = ExpectedToken::new(ExpectedToken::EMPTY, self.token.clone())
            .add_expects(self.expected_token_exps);

        if self.expected_token_exps.contains(ExpToken::Semi) {
            res.add_semi(self.prev_token.span);
        }

        self.expected_token_exps.clear();

        res
    }

    /// Look-ahead `dist` tokens away from `Parser::token`, when `dist == 0`, it
    /// is equivalent to accessing `Parser::token`.
    pub fn look_ahead<'a, R: 'a>(&'a self, dist: usize, looker: impl FnOnce(&'a Token) -> R) -> R {
        if dist == 0 {
            looker(&self.token)
        } else {
            looker(self.tokens.get(self.ti + dist))
        }
    }

    /// Look many (`N`) tokens ahead of `dist` tokens from the current one. If
    /// the number of token to look exceeds the number of tokens in the token
    /// stream it will return enough of the Eof token to make it `N` long.
    pub fn look_many_ahead<R, const N: usize>(
        &self,
        dist: usize,
        looker: impl FnOnce([&Token; N]) -> R,
    ) -> R {
        const {
            if N == 0 {
                panic!("cannot use look_many_ahead with N = 0.")
            } else if N == 1 {
                panic!("use look_ahead")
            }
        }

        let dist_abs = dist + self.ti;
        let cow: Cow<'_, [Token]> = self.tokens.get_slice(dist_abs..dist_abs + N);
        debug_assert_eq!(cow.len(), N);

        let slice: &[Token] = cow.as_ref();

        if cfg!(debug_assertions) && cow.is_empty() && N != 0 {
            panic!("failed to compute the length of the array to output")
        }

        let Ok(arr1): Result<&[Token; N], _> = slice.try_into() else {
            unreachable!()
        };

        let arr = arr1.each_ref();

        looker(arr)
    }

    /// Like [`Parser::look_many_ahead`] but gives access to the [`TokenType`]
    /// instead of the [`Token`].
    #[inline(always)]
    pub fn look_many_tt<R, const N: usize>(
        &self,
        dist: usize,
        looker: impl FnOnce([&TokenType; N]) -> R,
    ) -> R {
        self.look_many_ahead(dist, |t: [&Token; N]| {
            let tts = t.map(|t| &t.tt);
            looker(tts)
        })
    }

    /// Clones the location of the previous token, `Parser::prev_token`.
    #[inline(always)]
    pub fn token_span(&self) -> Span {
        self.prev_token.span
    }

    /// Return the literal contained in the previously parsed token,
    /// `Parser::prev_token`.
    ///
    /// # Safety
    ///
    /// Calling this function if `Parser::prev_token` isn't a
    /// [`TokenType::Lit`], can cause a UB.
    pub fn as_lit(&self) -> Lit {
        let Lit(lit) = &self.prev_token.tt else {
            unreachable!()
        };

        lit.clone()
    }

    /// Return the identifier (the string) contained in the previously parsed
    /// token, `Parser::prev_token`.
    ///
    /// # Safety
    ///
    /// Calling this function if `Parser::prev_token` isn't a
    /// [`TokenType::Ident`], it's a UB.
    pub fn as_ident(&self) -> Identifier {
        match self.prev_token {
            Token {
                tt: Ident(id),
                span,
            } => Identifier::new(id, span),
            Token { span, .. } if self.recovery => {
                // NOTE: in recovery we sometime try to have an ident that we
                // didn't had so here we are sending a dummy value.

                Identifier::new(sym::dummy, span)
            }
            _ => {
                unreachable!()
            }
        }
    }

    /// Return a result with `Err(Recovered::Yes(val, guarante))` if val is
    /// `Some(val)` or `Err(Recovered::No(guarantee))` otherwise, this function
    /// is guranteed to emit the current expected token diagnostic.
    #[track_caller]
    pub fn expdiag_bump<T>(&mut self, val: impl Into<Option<T>>) -> ReResult<T> {
        let diag = self.expected_diag();
        let guarantee = self.dcx.emit(diag);

        if let Some(val) = val.into() {
            return Err(Recovered::Yes(val, guarantee));
        } else {
            return Err(Recovered::No(guarantee));
        }
    }

    /// Parse a [`Path`].
    pub fn parse_path(&mut self) -> ReResult<Spanned<Path>> {
        let mut path = Path::new();

        if self.eat(ExpToken::Ident) {
            path.push(self.as_ident().name);
        } else if self.eat(ExpToken::KwPkg) {
            path.push_seg(PathSegment::Pkg);
        } else {
            // NB. use a dumb span.
            return self.expdiag_bump(respan(path, self.token.span));
        }

        let lo = self.token_span();
        let mut hi = lo;

        while self.eat_no_expect(ExpToken::ColonColon) {
            if self.eat(ExpToken::Ident) {
                path.push(self.as_ident().name);
                hi = self.token_span();
            } else {
                self.recovery = true;

                let mut diag = self.expected_diag().into_diag(&self.dcx);

                if self.check_no_expect(ExpToken::KwPkg) {
                    diag.messages.push(Message {
                        level: Level::Help,
                        msg: "'pkg' can only be used at the start of a path".to_string(),
                    });
                    path.push(sym::fakepkg);
                } else {
                    path.push(self.as_ident().name)
                }

                self.dcx.emit(diag);
                self.bump();
                hi = self.token_span();
            }
        }

        Ok(respan(path, Span::join(lo, hi)))
    }

    /// Parses [`Mutability`].
    pub fn parse_mutability(&mut self) -> Mutability {
        if self.eat_no_expect(ExpToken::KwMut) {
            Mutability::Mut
        } else {
            Mutability::Not
        }
    }

    /// Tries to recover parsing for [`Parser::parse_parenthesized`].
    ///
    /// After the recovery, `Parser::token` will be one of:
    /// - `Comma`
    /// - `RParen`
    /// - `Eof`
    pub fn recover_parenthesized_parsing(&mut self, guarantee: DiagGuaranteed) {
        _ = guarantee;
        let mut remaining_rparen = 0;

        while !(self.check_no_expect(ExpToken::Comma)
            || self.check_no_expect(ExpToken::RParen)
            || self.check_no_expect(ExpToken::Eof))
        {
            if self.check_no_expect(ExpToken::LParen) {
                remaining_rparen += 1;
            } else if self.check_no_expect(ExpToken::RParen) {
                if remaining_rparen == 0 {
                    // eat the )
                    self.bump();

                    break;
                } else {
                    remaining_rparen -= 1;
                }
            }

            self.bump();
        }
    }

    /// Parses something between parenthesis separated by a comma, can have a
    /// trailing comma before the last closing parenthesis.
    pub fn parse_parenthesized<T>(&mut self, parse_fn: ParsingFn<T>) -> ReResult<Spanned<Vec<T>>> {
        let mut nodes = Vec::new();
        let lo = self.expect(ExpToken::LParen).dere_or(|| self.token.span);

        loop {
            if self.eat_no_expect(ExpToken::RParen) {
                break;
            }

            match parse_fn(self).dere() {
                Ok(node) => nodes.push(node),
                Err(guarantee) => {
                    self.recovery = true;
                    self.recover_parenthesized_parsing(guarantee);
                }
            }

            if self.eat(ExpToken::Comma) {
                // ...
            } else if self.eat(ExpToken::RParen) {
                break;
            } else {
                // TODO: instead of returning early, maybe we should recover and
                // keep parsing.
                return self.expdiag_bump(None);
            }
        }

        let hi = self.token_span();

        Ok(respan(nodes, Span::join(lo, hi)))
    }

    /// Merges the current restrictions with the provided ones then call `f`,
    /// and after resets the restrictions to what was before.
    pub fn with_restrictions<R>(
        &mut self,
        new_rests: Restrictions,
        f: impl FnOnce(&mut Parser) -> R,
    ) -> R {
        let old = self.restrictions;
        self.restrictions |= new_rests;

        let val = f(self);

        self.restrictions = old;

        val
    }

    /// Parses to a module.
    pub fn produce(&mut self) -> ReResult<Module> {
        let module = tri!(self.parse_module());

        if let Some(guarantee) = self.dcx.has_emitted() {
            guarantee.recover_with(module)
        } else {
            Ok(module)
        }
    }
}

/// Look token used in [`Parser::look_ahead`]
pub fn look_tok(tok: &Token) -> &Token {
    tok
}

/// Look token type used in [`Parser::look_ahead`]
pub fn look_tt(tok: &Token) -> &TokenType {
    &tok.tt
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Restrictions: u8 {
        const STMT_EXPR = 1 << 0;
    }
}
