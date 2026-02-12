//! Statements and block in Muon

use super::*;

/// Muon statement
#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

/// Statement kind.
#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    /// Binding definition statement.
    ///
    /// `"let" "mut"? ident (":" type)? ( "=" expr )? ";"`
    BindingDef(Mutability, Identifier, Option<Type>, Option<Expr>),
    /// Expression statement.
    ///
    /// `expr_with_block ";"?` or
    /// `expr_without_block ";"`
    Expr(Expr),
}

impl StmtKind {
    /// Returns `true` if the stmt kind is [`Expr`].
    ///
    /// [`Expr`]: StmtKind::Expr
    #[must_use]
    pub fn is_expr(&self) -> bool {
        matches!(self, Self::Expr(..))
    }
}

/// A Muon Block.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Expr>,
    pub span: Span,
}

/// [`Stmt`] and [`Block`] parsing.
impl Parser {
    /// Parses a statement.
    pub fn parse_stmt(&mut self, in_block: bool) -> ReResult<Stmt> {
        match self.token.tt {
            Kw(Keyword::Let) => self.parse_binding_stmt(),
            _ => {
                // didn't recognized a statement, must be an expression statement
                self.parse_expr_stmt(in_block)
            }
        }
    }

    /// Parses a binding statement
    pub fn parse_binding_stmt(&mut self) -> ReResult<Stmt> {
        let lo = tri!(self.expect(ExpToken::KwLet));

        let mutability = self.parse_mutability();

        tri!(self.expect(ExpToken::Ident));

        let name = self.as_ident();

        let typ = if self.eat_no_expect(ExpToken::Colon) {
            Some(tri!(self.parse_type()))
        } else {
            None
        };

        let val = if self.eat_no_expect(ExpToken::Eq) {
            Some(tri!(self.parse_expr()))
        } else {
            None
        };

        let hi = tri!(self.expect(ExpToken::Semi));

        Ok(Stmt {
            kind: StmtKind::BindingDef(mutability, name, typ, val),
            span: Span::join(lo, hi),
        })
    }

    /// Parses an expression statement
    pub fn parse_expr_stmt(&mut self, in_block: bool) -> ReResult<Stmt> {
        let expr =
            tri!(self.with_restrictions(Restrictions::STMT_EXPR, |parser| parser.parse_expr()));
        let lo = expr.span;

        let hi = if expr.kind.contains_block() {
            if self.eat_no_expect(ExpToken::Semi) {
                self.prev_token.span
            } else {
                expr.span
            }
        } else {
            // all of this for the tail expression of a block
            if in_block {
                if self.check(ExpToken::Semi) {
                    self.bump();
                    self.token_span()
                } else {
                    self.expr_semi_diag = Some(self.expected_diag());
                    expr.span
                }
            } else {
                tri!(self.expect(ExpToken::Semi))
            }
        };

        Ok(Stmt {
            kind: StmtKind::Expr(expr),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a block.
    pub fn parse_block(&mut self) -> ReResult<Block> {
        let mut stmts: Vec<Stmt> = Vec::new();
        let mut tail: Option<Expr> = None;

        let lo = tri!(self.expect(ExpToken::LCurly));

        loop {
            if self.eat_one_of(None, [ExpToken::RCurly, ExpToken::Eof]) {
                break;
            }

            let stmt = match self.parse_stmt(true).dere() {
                Ok(stmt) => stmt,
                Err(guarantee) => {
                    self.recovery = true;
                    self.recover_stmt_in_block(guarantee);

                    continue;
                }
            };

            let curly = self.check_no_expect(ExpToken::RCurly);
            let is_expr = stmt.kind.is_expr();

            match (curly, is_expr, self.expr_semi_diag.take()) {
                (true, true, diag) => {
                    // ... expr }
                    //         ^ we are here so:
                    let Stmt {
                        kind: StmtKind::Expr(expr),
                        span: _,
                    } = stmt
                    else {
                        unreachable!()
                    };
                    debug_assert!(diag.is_some());

                    tail = Some(expr);
                    break;
                }
                (.., diag) => {
                    // one of:
                    //
                    // 1. ... stmt }
                    //            ^ here
                    //   if curly == true && is_expr == false
                    //
                    // 2. ... expr ";"? ...
                    //                 ^ here
                    //   if curly == fale && is_expr == true
                    //
                    // 3. ... stmt ...
                    //            ^ here
                    //   if curly == fale && is_expr == false
                    //
                    // so:

                    if let Some(diag) = diag {
                        self.dcx.emit(diag);
                    }

                    stmts.push(stmt);
                }
            }
        }

        let hi = tri!(self.expect(ExpToken::RCurly));

        Ok(Block {
            stmts,
            tail,
            span: Span::join(lo, hi),
        })
    }

    /// Tries to recover the parsing of statements in a block.
    ///
    /// The parser is bumped until prev_token is one of `is_stmt_separator`.
    /// It's smart so he knows about opening and closing curly.
    ///
    /// After recovery, we have the two possible cases:
    /// - we keep parsing stmt / the last_expr
    /// - we are in front of the RCurly, either because the faulty stmt was the
    ///   last one or the recovery failed to do something better.
    pub fn recover_stmt_in_block(&mut self, guarantee: DiagGuaranteed) {
        _ = guarantee;
        let mut remaining_rcurly = 0;

        while (!self.token.tt.is_stmt_separator() || self.check_no_expect(ExpToken::RCurly))
            && !self.check_no_expect(ExpToken::Eof)
        {
            if self.check_no_expect(ExpToken::LCurly) {
                remaining_rcurly += 1;
            } else if self.check_no_expect(ExpToken::RCurly) {
                if remaining_rcurly == 0 {
                    // eat the }
                    self.bump();

                    break;
                } else {
                    remaining_rcurly -= 1;
                }
            }

            self.bump();
        }

        self.bump();
    }
}
