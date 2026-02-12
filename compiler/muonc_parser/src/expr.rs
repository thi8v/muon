//! Muon's expression

use std::fmt;

use crate::diags::{MalformedIfExpr, MalformedIfKind};

use super::*;

/// The associativity, is used to parse the binary operations
#[derive(Clone, Debug, PartialEq)]
pub enum Associativity {
    LeftToRight,
    RightToLeft,
    None,
}

/// Muon expression
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    /// Create a dummy expression
    pub fn dummy() -> Expr {
        let mut lit = Lit::int(u128::MAX);
        lit.tag = Some(sym::dummy);

        Expr {
            kind: ExprKind::Lit(lit),
            span: DUMMY_SP,
        }
    }
}

/// Expression kind.
#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    /// boolean literal expression
    ///
    /// `true` / `false`
    Bool(bool),
    /// literal expression
    ///
    /// `integer` / `float` / `string` / `char`
    Lit(Lit),
    /// parenthesis expression
    ///
    /// `"(" expr ")"`
    Paren(Box<Expr>),
    /// path expression
    ///
    /// `path`
    Path(Path),
    /// binary expression
    ///
    /// `expr binop expr`
    Binary(Box<Expr>, BinOp, Box<Expr>),
    /// unary expression
    ///
    /// `unop expr` / `expr unop`
    Unary(UnOp, Box<Expr>),
    /// (mutable) borrow expression
    ///
    /// `"&" "mut"? expr`
    Borrow(Mutability, Box<Expr>),
    /// call expression
    ///
    /// **NB**: the span of this expression is just on the parenthesis:
    /// ```muon
    ///    foo(bar, baz)
    /// //    ^^^^^^^^^^ the span
    /// ```
    ///
    /// `expr "(" ( expr ),* ")"`
    Call(Box<Expr>, Vec<Expr>),
    /// if-else expression
    ///
    /// `"if" expr block ( "else" (block | if_expr) )?` or
    /// `"if" "(" expr ")" expr "else" expr`
    If(IfFlavor, Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    /// block expression
    ///
    /// `label_def? block`
    Block(LabelDef, Box<Block>),
    /// while expression
    ///
    /// `label_def? "while" expr block`
    While(LabelDef, Box<Expr>, Box<Block>),
    /// for expression
    ///
    /// `label_def? "for" ident "in" expr block`
    For(LabelDef, Identifier, Box<Expr>, Box<Block>),
    /// loop expression
    ///
    /// `label_def? "loop" block`
    Loop(LabelDef, Box<Block>),
    /// return expression
    ///
    /// `"return" expr?`
    Return(Option<Box<Expr>>),
    /// break expression
    ///
    /// `"break" label_use? expr?`
    Break(LabelUse, Option<Box<Expr>>),
    /// continue expression
    ///
    /// `"continue" label_use?`
    Continue(LabelUse),
    /// field expression
    ///
    /// `expr "." ident`
    Field(Box<Expr>, Identifier),
    /// cast expression
    ///
    /// `expr "as" type`
    Cast(Box<Expr>, Type),
}

impl ExprKind {
    /// Returns `true` if the expr kind contains a [`Block`].
    ///
    /// [`Block`]: ExprKind::Block
    #[must_use]
    pub fn contains_block(&self) -> bool {
        matches!(
            self,
            Self::Block(..)
                | Self::If(IfFlavor::Block, ..)
                | Self::While(..)
                | Self::For(..)
                | Self::Loop(..)
        )
    }
}

/// The precedence table of Lun
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    // `__First__` is a special precedence value, it is used to exit out of the
    // loop when a non expression token is after an expression. It is not the
    // `HIGHEST_PRECEDENCE` for the same reason.
    #[doc(hidden)]
    __First__,
    // /!\ Attention /!\
    //
    // If you change the highest precedence in this enumeration change the
    // HIGHEST_PRECEDENCE constant
    //
    /// `a = b`
    Assignment,
    /// `a or b`
    LogicalOr,
    /// `a and b`
    LogicalAnd,
    /// `a < b ; a > b ; a <= b ; a >= b`
    Comparison,
    /// `a == b ; a != b`
    Equality,
    /// `a | b`
    BitwiseOr,
    /// `a ^ b`
    BitwiseXor,
    /// `a & b`
    BitwiseAnd,
    /// `a >> b ; a << b`
    Shift,
    /// `a + b ; a - b`
    Term,
    /// `a * b ; a / b ; a % b`
    Factor,
    /// `expr "as" type`
    Cast,
    /// `op expression`
    Unary,
    /// `expression "(" expression,* ")"`
    Call,
    /// `expression "." ident`
    Field,
    /// `intlit "true" "false" charlit strlit group`
    Primary,
    // Like `__First__` it is a special variant of `Precedence` that should
    // never be used.
    #[doc(hidden)]
    __Last__,
}

impl Precedence {
    /// Returns the [`Precedence`] following the one passed as arg.
    pub fn next(self) -> Precedence {
        match self {
            Self::__First__ => Self::Assignment,
            Self::Assignment => Self::LogicalOr,
            Self::LogicalOr => Self::LogicalAnd,
            Self::LogicalAnd => Self::Comparison,
            Self::Comparison => Self::Equality,
            Self::Equality => Self::BitwiseOr,
            Self::BitwiseOr => Self::BitwiseXor,
            Self::BitwiseXor => Self::BitwiseAnd,
            Self::BitwiseAnd => Self::Shift,
            Self::Shift => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Cast,
            Self::Cast => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::Field,
            Self::Field => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    /// Get the associativity of the corresponding precedence.
    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Assignment => Associativity::RightToLeft,
            Self::LogicalOr => Associativity::LeftToRight,
            Self::LogicalAnd => Associativity::LeftToRight,
            Self::Comparison => Associativity::LeftToRight,
            Self::Equality => Associativity::LeftToRight,
            Self::BitwiseOr => Associativity::LeftToRight,
            Self::BitwiseXor => Associativity::LeftToRight,
            Self::BitwiseAnd => Associativity::LeftToRight,
            Self::Shift => Associativity::LeftToRight,
            Self::Term => Associativity::LeftToRight,
            Self::Factor => Associativity::LeftToRight,
            Self::Cast => Associativity::LeftToRight,
            Self::Unary => Associativity::RightToLeft,
            Self::Call => Associativity::LeftToRight,
            Self::Field => Associativity::LeftToRight,
            Self::Primary => Associativity::LeftToRight,
            Self::__Last__ | Self::__First__ => unreachable!(),
        }
    }
}

impl Precedence {
    pub fn from_tt(value: &TokenType) -> Option<Precedence> {
        match value {
            Eq => Some(Precedence::Assignment),
            AndAnd => Some(Precedence::LogicalOr),
            OrOr => Some(Precedence::LogicalAnd),
            Lt | Gt | LtEq | GtEq => Some(Precedence::Comparison),
            EqEq | BangEq => Some(Precedence::Equality),
            Or => Some(Precedence::BitwiseOr),
            Caret => Some(Precedence::BitwiseXor),
            And => Some(Precedence::BitwiseAnd),
            LtLt | GtGt => Some(Precedence::Shift),
            Plus | Minus => Some(Precedence::Term),
            Star | Slash | Percent => Some(Precedence::Factor),
            Kw(Keyword::As) => Some(Precedence::Cast),
            LParen => Some(Precedence::Call),
            Dot => Some(Precedence::Field),
            DotStar => Some(Precedence::Primary),
            _ => None,
        }
    }
}

/// The highest precedence of [`Precedence`]
pub const HIGHEST_PRECEDENCE: Precedence = Precedence::Assignment;

/// If expression flavor
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IfFlavor {
    /// `"if" expr block ( "else" block )?`
    Block,
    /// `"if" "(" expr ")" expr "else" expr`
    Expression,
}

impl fmt::Display for IfFlavor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IfFlavor::Block => write!(f, "block"),
            IfFlavor::Expression => write!(f, "expression"),
        }
    }
}

/// Label definition, grammar: `( ident ":" )?`
#[derive(Debug, Clone, PartialEq)]
pub struct LabelDef(pub Option<Spanned<Identifier>>);

impl LabelDef {
    /// Get the span of the label def.
    pub fn span(&self) -> Option<Span> {
        self.0.as_ref().map(|l| l.span)
    }
}

/// Label use, grammar: `( ":" ident )?`
#[derive(Debug, Clone, PartialEq)]
pub struct LabelUse(pub Option<Spanned<Identifier>>);

impl LabelUse {
    /// Get the span of the label use.
    pub fn span(&self) -> Option<Span> {
        self.0.as_ref().map(|l| l.span)
    }
}

/// [`Expr`] parsing.
impl Parser {
    /// Make an expression based on the kind with the span of the prev_token.
    pub fn mk_expr(&self, kind: ExprKind) -> Expr {
        Expr {
            kind,
            span: self.token_span(),
        }
    }

    /// Make an expression out of a block.
    pub fn mk_block_expr(&self, block: Block) -> Expr {
        Expr {
            span: block.span,
            kind: ExprKind::Block(LabelDef(None), Box::new(block)),
        }
    }

    /// Parses a label definition
    pub fn parse_label_def(&mut self) -> ReResult<LabelDef> {
        if self.eat_no_expect(ExpToken::Ident) {
            let label = self.as_ident();
            let lo = label.span;
            let hi = tri!(self.expect(ExpToken::Colon));

            Ok(LabelDef(Some(Spanned {
                node: label,
                span: Span::join(lo, hi),
            })))
        } else {
            Ok(LabelDef(None))
        }
    }

    /// Parses a label use
    pub fn parse_label_use(&mut self) -> ReResult<LabelUse> {
        if self.eat_no_expect(ExpToken::Colon) {
            let lo = self.token_span();
            let hi = tri!(self.expect(ExpToken::Ident));
            let label = self.as_ident();

            Ok(LabelUse(Some(Spanned {
                node: label,
                span: Span::join(lo, hi),
            })))
        } else {
            Ok(LabelUse(None))
        }
    }

    /// Parses an expression.
    pub fn parse_expr(&mut self) -> ReResult<Expr> {
        self.parse_expr_precedence(HIGHEST_PRECEDENCE)
    }

    /// Returns `"expression"` or `"statement"` if `Restrictions::EXPR_STMT` is true.
    pub fn expr_str(&self) -> &'static str {
        "expression"
    }

    /// Parses an expression with the appropriate precedence.
    pub fn parse_expr_precedence(&mut self, precedence: Precedence) -> ReResult<Expr> {
        let mut lhs = tri!(match self.token.tt {
            Lit(_) => self.parse_lit_expr(),
            Kw(Keyword::True | Keyword::False) => self.parse_bool_expr(),
            LParen => self.parse_paren_expr(),
            Ident(_) => self.parse_ident_expr(),
            Kw(Keyword::Pkg) => self.parse_path_expr(),
            Kw(Keyword::If) => self.parse_if_expr(None),
            Kw(Keyword::While) => self.parse_while_expr(),
            Kw(Keyword::Loop) => self.parse_loop_expr(),
            Kw(Keyword::For) => self.parse_for_expr(),
            LCurly => self.parse_block_expr(),
            Kw(Keyword::Return) => self.parse_return_expr(),
            Kw(Keyword::Break) => self.parse_break_expr(),
            Kw(Keyword::Continue) => self.parse_continue_expr(),
            And => self.parse_borrow_expr(),
            ref tt if UnOp::left_from_token(tt).is_some() => self.parse_left_unary_expr(),
            _ => {
                self.bump();

                self.dcx
                    .emit(ExpectedToken::new(
                        [self.expr_str()],
                        self.prev_token.clone(),
                    ))
                    .cant_rec()
            }
        });

        loop {
            let Some(cur_pr) = Precedence::from_tt(&self.token.tt) else {
                // the next token isn't the start of a "post" expression
                break;
            };

            if precedence > cur_pr {
                break;
            }

            lhs = tri!(match self.token.tt {
                LParen => self.parse_call_expr(Box::new(lhs)),
                Dot => self.parse_field_expr(Box::new(lhs)),
                Kw(Keyword::As) => self.parse_cast_expr(Box::new(lhs)),
                ref tt if BinOp::from_tt(tt).is_some() => self.parse_binary_expr(Box::new(lhs)),
                ref tt if UnOp::right_from_token(tt).is_some() =>
                    self.parse_right_unary_expr(Box::new(lhs)),
                _ => break,
            });
        }

        Ok(lhs)
    }

    // Parsing of "primary" expression

    /// Parses literal expressions.
    pub fn parse_lit_expr(&mut self) -> ReResult<Expr> {
        if let Some(lit) = self.eat_lit() {
            Ok(self.mk_expr(ExprKind::Lit(lit)))
        } else {
            self.bump();

            Err(Recovered::No(self.dcx.emit(ExpectedToken::new(
                ["literal"],
                self.prev_token.clone(),
            ))))
        }
    }

    /// Parses a boolean expression
    pub fn parse_bool_expr(&mut self) -> ReResult<Expr> {
        if self.eat(ExpToken::KwTrue) {
            Ok(self.mk_expr(ExprKind::Bool(true)))
        } else if self.eat(ExpToken::KwFalse) {
            Ok(self.mk_expr(ExprKind::Bool(false)))
        } else {
            // fail but recoverable with dummy value
            self.expdiag_bump(self.mk_expr(ExprKind::Bool(false)))
        }
    }

    /// Parses a parenthesized expression
    pub fn parse_paren_expr(&mut self) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::LParen));

        let expr = Box::new(tri!(self.parse_expr()));

        let hi = tri!(self.expect(ExpToken::RParen));

        Ok(Expr {
            kind: ExprKind::Paren(expr),
            span: Span::join(lo, hi),
        })
    }

    /// Checks for a labeled expression.
    pub fn is_labeled_expr(&mut self) -> bool {
        self.look_many_tt::<_, 2>(1, |tts| {
            matches!(
                tts,
                [
                    Colon,
                    Kw(Keyword::While | Keyword::For | Keyword::Loop) | LCurly
                ]
            )
        })
    }

    /// Parses expressions that start with an ident.
    pub fn parse_ident_expr(&mut self) -> ReResult<Expr> {
        if self.is_labeled_expr() {
            match self.look_ahead(2, look_tt) {
                Kw(Keyword::While) => self.parse_while_expr(),
                Kw(Keyword::Loop) => self.parse_loop_expr(),
                Kw(Keyword::For) => self.parse_for_expr(),
                LCurly => self.parse_block_expr(),
                _ => unreachable!(),
            }
        } else {
            self.parse_path_expr()
        }
    }

    /// Parses a path expression.
    pub fn parse_path_expr(&mut self) -> ReResult<Expr> {
        let path = tri!(self.parse_path());

        Ok(Expr {
            kind: ExprKind::Path(path.node),
            span: path.span,
        })
    }

    /// Parses an if expression, if `exp_flavor` is set to something this
    /// function will only parse an if expression with this flavor.
    pub fn parse_if_expr(&mut self, exp_flavor: Option<IfFlavor>) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::KwIf));

        let cond = tri!(self.parse_expr());

        let flavor;

        let (then_e, else_e, hi) = if let ExprKind::Paren(_) = cond.kind {
            // `"if" "(" expr ")" expr "else" expr`
            //                   ^ here
            flavor = IfFlavor::Expression;

            let then_e = Box::new(tri!(self.parse_expr()));

            self.expect(ExpToken::KwElse).discard();

            let else_e = tri!(self.parse_expr());
            let hi = else_e.span;
            let else_e = Some(Box::new(else_e));

            (then_e, else_e, hi)
        } else {
            // `"if" expr block ( "else" block )?`
            //           ^ here
            flavor = IfFlavor::Block;

            let then_b = tri!(self.parse_block());
            let then_e = Box::new(self.mk_block_expr(then_b));

            if self.eat_no_expect(ExpToken::KwElse) {
                if self.check(ExpToken::LCurly) {
                    // `"if" expr block "else" block`
                    //                        ^ here
                    let else_b = tri!(self.parse_block());
                    let else_e = Box::new(self.mk_block_expr(else_b));
                    let hi = else_e.span;

                    (then_e, Some(else_e), hi)
                } else if self.check(ExpToken::KwIf) {
                    // `"if" expr block "else" if ...`
                    //                        ^ here

                    let if_expr = Box::new(tri!(self.parse_if_expr(Some(IfFlavor::Block))));
                    let hi = if_expr.span;

                    (then_e, Some(if_expr), hi)
                } else {
                    // NB: return a dummy value
                    return self.expdiag_bump(Expr {
                        kind: ExprKind::If(flavor, Box::new(cond), then_e, None),
                        span: Span::join(lo, self.token_span()),
                    });
                }
            } else {
                let hi = then_e.span;

                (then_e, None, hi)
            }
        };

        let span = Span::join(lo, hi);

        if let Some(exp_flavor) = exp_flavor
            && exp_flavor != flavor
        {
            self.dcx
                .emit(MalformedIfExpr {
                    kind: MalformedIfKind::BlockElseIfExpr,
                    primary: span,
                })
                .discard();
        }

        Ok(Expr {
            kind: ExprKind::If(flavor, Box::new(cond), then_e, else_e),
            span,
        })
    }

    /// Parses a while expression with a potential leading label.
    pub fn parse_while_expr(&mut self) -> ReResult<Expr> {
        let label_def = tri!(self.parse_label_def());

        let while_span = tri!(self.expect(ExpToken::KwWhile));
        let lo = label_def.span().unwrap_or(while_span);

        let cond = Box::new(tri!(self.parse_expr()));

        let block = Box::new(tri!(self.parse_block()));
        let hi = block.span;

        Ok(Expr {
            kind: ExprKind::While(label_def, cond, block),
            span: Span::join(lo, hi),
        })
    }

    /// Parses an infinite loop expression with a potential leading label.
    pub fn parse_loop_expr(&mut self) -> ReResult<Expr> {
        let label_def = tri!(self.parse_label_def());

        let loop_span = tri!(self.expect(ExpToken::KwLoop));
        let lo = label_def.span().unwrap_or(loop_span);

        let block = Box::new(tri!(self.parse_block()));
        let hi = block.span;

        Ok(Expr {
            kind: ExprKind::Loop(label_def, block),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a for loop expression with maybe a leading label.
    pub fn parse_for_expr(&mut self) -> ReResult<Expr> {
        let label_def = tri!(self.parse_label_def());

        let for_span = tri!(self.expect(ExpToken::KwFor));
        let lo = label_def.span().unwrap_or(for_span);

        tri!(self.expect(ExpToken::Ident));
        let ident = self.as_ident();

        tri!(self.expect(ExpToken::KwIn));

        let iter = Box::new(tri!(self.parse_expr()));

        let block = Box::new(tri!(self.parse_block()));
        let hi = block.span;

        Ok(Expr {
            kind: ExprKind::For(label_def, ident, iter, block),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a block expression with a potential leading label.
    pub fn parse_block_expr(&mut self) -> ReResult<Expr> {
        let label_def = tri!(self.parse_label_def());

        let block = Box::new(tri!(self.parse_block()));

        let lo = label_def.span().unwrap_or(block.span);
        let hi = block.span;

        Ok(Expr {
            kind: ExprKind::Block(label_def, block),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a return expression
    pub fn parse_return_expr(&mut self) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::KwReturn));
        let mut hi = lo;

        let expr = if self.token.tt.is_stmt_separator() {
            None
        } else {
            let expr = Box::new(self.parse_expr().dere_or(Expr::dummy));
            hi = expr.span;

            Some(expr)
        };

        Ok(Expr {
            kind: ExprKind::Return(expr),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a break expression
    pub fn parse_break_expr(&mut self) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::KwBreak));
        let mut hi = lo;

        let label_use = tri!(self.parse_label_use());

        if let Some(span) = label_use.span() {
            hi = span;
        }

        let expr = if self.token.tt.is_stmt_separator() {
            None
        } else {
            let expr = Box::new(self.parse_expr().dere_or(Expr::dummy));
            hi = expr.span;

            Some(expr)
        };

        Ok(Expr {
            kind: ExprKind::Break(label_use, expr),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a continue expression
    pub fn parse_continue_expr(&mut self) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::KwContinue));

        let label_use = tri!(self.parse_label_use());
        let hi = label_use.span().unwrap_or(lo);

        Ok(Expr {
            kind: ExprKind::Continue(label_use),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a borrow expression
    pub fn parse_borrow_expr(&mut self) -> ReResult<Expr> {
        let lo = tri!(self.expect(ExpToken::And));

        let mutability = self.parse_mutability();

        let expr = Box::new(tri!(self.parse_expr()));
        let hi = expr.span;

        Ok(Expr {
            kind: ExprKind::Borrow(mutability, expr),
            span: Span::join(lo, hi),
        })
    }

    // Parsing of expressions with some precedence in mind

    /// Parses a unary left expression
    pub fn parse_left_unary_expr(&mut self) -> ReResult<Expr> {
        let (unop, lo) = if let Some(op) = UnOp::left_from_token(&self.token.tt) {
            self.bump();
            (op, self.token_span())
        } else {
            return self
                .dcx
                .emit(ExpectedToken::new(["unary operator"], self.token.clone()))
                .cant_rec();
        };

        let expr = Box::new(tri!(self.parse_expr()));
        let hi = expr.span;

        Ok(Expr {
            kind: ExprKind::Unary(unop, expr),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a call expression with the given callee.
    pub fn parse_call_expr(&mut self, callee: Box<Expr>) -> ReResult<Expr> {
        let args = self
            .parse_parenthesized(Parser::parse_expr)
            .dere_or(|| Spanned {
                node: Vec::new(),
                span: callee.span,
            });

        Ok(Expr {
            kind: ExprKind::Call(callee, args.node),
            span: args.span,
        })
    }

    /// Parses a field expression with the given operand
    pub fn parse_field_expr(&mut self, operand: Box<Expr>) -> ReResult<Expr> {
        let lo = operand.span;

        self.expect(ExpToken::Dot).discard();

        let hi = tri!(self.expect(ExpToken::Ident));
        let member = self.as_ident();

        Ok(Expr {
            kind: ExprKind::Field(operand, member),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a binary expression
    pub fn parse_binary_expr(&mut self, lhs: Box<Expr>) -> ReResult<Expr> {
        let lo = lhs.span;

        let (binop, tt) = match BinOp::from_tt(&self.token.tt) {
            Some(op) => {
                self.bump();
                let tt = &self.prev_token.tt;

                (op, tt)
            }
            None => {
                return self
                    .dcx
                    .emit(ExpectedToken::new(["binary operator"], self.token.clone()))
                    .cant_rec();
            }
        };

        let Some(mut pr) = Precedence::from_tt(tt) else {
            // NB we are sure because we just checked that tt was a binary
            // operator.
            unreachable!();
        };

        if pr.associativity() == Associativity::LeftToRight {
            pr = pr.next();
        }

        let rhs = Box::new(self.parse_expr_precedence(pr).dere_or(Expr::dummy));
        let hi = rhs.span;

        Ok(Expr {
            kind: ExprKind::Binary(lhs, binop, rhs),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a right unary expression
    pub fn parse_right_unary_expr(&mut self, operand: Box<Expr>) -> ReResult<Expr> {
        let lo = operand.span;

        let (unop, hi) = if let Some(op) = UnOp::right_from_token(&self.token.tt) {
            self.bump();

            (op, self.token_span())
        } else {
            return self
                .dcx
                .emit(ExpectedToken::new(["unary operator"], self.token.clone()))
                .cant_rec();
        };

        Ok(Expr {
            kind: ExprKind::Unary(unop, operand),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a cast expression
    pub fn parse_cast_expr(&mut self, operand: Box<Expr>) -> ReResult<Expr> {
        let lo = operand.span;

        self.expect(ExpToken::KwAs).discard();

        let typ = tri!(self.parse_type());
        let hi = typ.span;

        Ok(Expr {
            kind: ExprKind::Cast(operand, typ),
            span: Span::join(lo, hi),
        })
    }
}
