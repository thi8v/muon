//! Parsing of Muon's items

use std::str::FromStr;

use crate::diags::{InvalidAbi, MutQualifierNotPermitted, VisQualifierNotPermitted};

use super::*;

/// Muon module, a collection of [`Item`]s that may be in a file or in a module
/// directive.
#[derive(Debug, Clone)]
pub struct Module {
    pub items: Vec<Item>,
    pub fid: FileId,
}

/// Visibility
///
/// NB: `T` is used to add a potential Span to the public variant of this enum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Visibility<T = ()> {
    Public(T),
    Private,
}

impl<T> Visibility<T> {
    /// Turns a `Visibility<T>` into a `Visibility` with a `T = ()` implied.
    pub fn simplify(self) -> Visibility<()> {
        match self {
            Visibility::Public(_) => Visibility::Public(()),
            Visibility::Private => Visibility::Private,
        }
    }

    /// Get the value inside of the public variant
    pub fn as_val(&self) -> Option<&T> {
        if let Self::Public(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

/// Muon item
#[derive(Debug, Clone)]
pub enum Item {
    /// Function definition
    ///
    /// *NB: the first span is the span from `fun` to `)` and the last span is
    /// the span of the entire item.*
    ///
    /// `vis? ident "::" "fun" "(" ( ident ":" type ),* ")" ( "->" type )? block`
    Fundef(Visibility, Identifier, Sig, Block, Span),
    /// Function declaration
    ///
    /// *NB: the first span is the span from `fun` to `)` and the last span is
    /// the span of the entire item.*
    ///
    /// `vis? ident "::" "fun" "(" ( ident ":" type ),* ")" ( "->" type )? ";"`
    Fundecl(Visibility, Identifier, Sig, Span),
    /// Global definition
    ///
    /// `vis? "mut"? ident (":" type)? "=" expr ";"`
    Globdef(Visibility, Mutability, Identifier, Option<Type>, Expr, Span),
    /// Global declaration
    ///
    /// `vis? "mut"? ident ":" type ";"`
    Globdecl(Visibility, Mutability, Identifier, Type, Span),
    /// Extern block
    ///
    /// `"extern" strlit "{" item* "}"`
    Extern(Abi, Vec<Item>, Span),
    /// Directive
    ///
    /// `directive`
    Directive(Directive),
}

/// Function definition parameter
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Identifier,
    pub typ: Type,
    pub span: Span,
}

/// Function definition / declaration signature
#[derive(Debug, Clone)]
pub struct Sig {
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub span: Span,
}

/// [`Item`] and [`Module`] parsing
impl Parser {
    /// Parses a module
    pub fn parse_module(&mut self) -> ReResult<Module> {
        Ok(Module {
            items: tri!(self.parse_item_seq()),
            fid: self.fid,
        })
    }

    /// Parses a sequence of items
    pub fn parse_item_seq(&mut self) -> ReResult<Vec<Item>> {
        let mut items = Vec::new();

        while !self.eat_one_of(None, [ExpToken::RCurly, ExpToken::Eof]) {
            match self.parse_item().dere() {
                Ok(item) => items.push(item),
                Err(guarantee) => {
                    self.recovery = true;
                    self.recover_item_in_container(ItemContainer::Module, guarantee);
                }
            }
        }

        Ok(items)
    }

    /// Tries to recover the parsing of an Item in `container`.
    ///
    /// The parser is bump until `self.token` is `token.can_begin_item() ==
    /// true`. If `container == ItemContainer::ExternBlock` it also returns when
    /// `self.token` is a `RCurly` that matches the first `LCurly`:
    ///
    /// ```muon
    /// extern "C" {
    ///
    /// // ...
    /// {}
    /// // ...
    ///
    /// } // the parser will recover until here even tho there was a } before
    ///   // but it was preceded by a {
    /// ```
    pub fn recover_item_in_container(
        &mut self,
        container: ItemContainer,
        guarantee: DiagGuaranteed,
    ) {
        _ = guarantee;

        // amount of } remaining until the one that will break the loop
        let mut remaining_rcurly = 0;

        while !self.token.tt.can_begin_item() && !self.check_no_expect(ExpToken::Eof) {
            if container == ItemContainer::ExternBlock {
                if self.check_no_expect(ExpToken::LCurly) {
                    remaining_rcurly += 1;
                } else if self.check_no_expect(ExpToken::RCurly) {
                    if remaining_rcurly == 0 {
                        break;
                    } else {
                        remaining_rcurly -= 1;
                    }
                }
            }

            self.bump();
        }
    }

    /// Parses the visibility
    pub fn parse_vis(&mut self) -> Visibility<Span> {
        if self.eat_no_expect(ExpToken::KwPub) {
            Visibility::Public(self.token_span())
        } else {
            Visibility::Private
        }
    }

    /// Returns `true` if the tokens following the current one who is the
    /// identifier, matches the grammar of a globdef/globdecl
    pub fn is_glob(&self) -> bool {
        self.look_ahead(1, |tok| matches!(tok.tt, Colon | Eq | Semi))
    }

    /// Parses an item
    pub fn parse_item(&mut self) -> ReResult<Item> {
        let vis = self.parse_vis();

        let mutability = self.parse_mutability();
        let mutability = (mutability, mutability.is_mut().then(|| self.token_span()));

        match self.token.tt {
            Ident(_) if self.look_ahead(1, |tok| matches!(tok.tt, ColonColon)) => {
                self.parse_fun_item(vis, mutability)
            }
            Ident(_) if self.is_glob() => self.parse_glob_item(vis, mutability),
            Kw(Keyword::Extern) => self.parse_extern_item(vis, mutability),
            Pound => self.parse_directive_item(),
            _ => {
                self.bump();

                self.dcx
                    .emit(ExpectedToken::new(["item"], self.prev_token.clone()))
                    .cant_rec()
            }
        }
    }

    /// Parses a fundef/fundecl parameter
    pub fn parse_param(&mut self) -> ReResult<Param> {
        let lo = tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        self.expect(ExpToken::Colon).discard();

        let typ = tri!(self.parse_type());
        let hi = typ.span;

        Ok(Param {
            name,
            typ,
            span: Span::join(lo, hi),
        })
    }

    /// Parses a fundef/fundecl item.
    pub fn parse_fun_item(
        &mut self,
        vis: Visibility<Span>,
        mutability: (Mutability, Option<Span>),
    ) -> ReResult<Item> {
        if let (Mutability::Mut, Some(mut_span)) = mutability {
            self.dcx
                .emit(MutQualifierNotPermitted { primary: mut_span });
        }

        let name_span = tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        let lo = if let Visibility::Public(span) = vis {
            span
        } else {
            name_span
        };

        tri!(self.expect(ExpToken::ColonColon));

        let sig_lo = tri!(self.expect(ExpToken::KwFun));

        let params = tri!(self.parse_parenthesized(Parser::parse_param));

        let ret = if self.eat_no_expect(ExpToken::MinusGt) {
            Some(tri!(self.parse_type()))
        } else {
            None
        };

        let sig_hi = ret.as_ref().map(|r| r.span).unwrap_or(params.span);

        let sig = Sig {
            params: params.node,
            ret,
            span: Span::join(sig_lo, sig_hi),
        };

        if self.check(ExpToken::LCurly) {
            let block = tri!(self.parse_block());
            let hi = block.span;

            Ok(Item::Fundef(
                vis.simplify(),
                name,
                sig,
                block,
                Span::join(lo, hi),
            ))
        } else if self.check(ExpToken::Semi) {
            let hi = tri!(self.expect(ExpToken::Semi));

            Ok(Item::Fundecl(vis.simplify(), name, sig, Span::join(lo, hi)))
        } else {
            let span = Span::join(lo, sig.span);

            // NB: return a dumb item
            self.expdiag_bump(Item::Fundecl(vis.simplify(), name, sig, span))
        }
    }

    /// Parses a globdef/globdecl item.
    pub fn parse_glob_item(
        &mut self,
        vis: Visibility<Span>,
        mutability: (Mutability, Option<Span>),
    ) -> ReResult<Item> {
        let name_span = tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        let lo = vis.as_val().copied().or(mutability.1).unwrap_or(name_span);

        let typ = if self.eat_no_expect(ExpToken::Colon) {
            Some(tri!(self.parse_type()))
        } else {
            None
        };

        let expr = if self.eat_no_expect(ExpToken::Eq) {
            Some(tri!(self.parse_expr()))
        } else {
            None
        };

        let hi = tri!(self.expect(ExpToken::Semi));

        match (typ, expr) {
            (typ, Some(expr)) => Ok(Item::Globdef(
                vis.simplify(),
                mutability.0,
                name,
                typ,
                expr,
                Span::join(lo, hi),
            )),
            (Some(typ), None) => Ok(Item::Globdecl(
                vis.simplify(),
                mutability.0,
                name,
                typ,
                Span::join(lo, hi),
            )),
            (None, None) => self
                .dcx
                .emit(ExpectedToken::new(
                    [ExpToken::Colon, ExpToken::Eq],
                    Token {
                        tt: TokenType::Semi,
                        span: hi,
                    },
                ))
                .recover_with(Item::Globdef(
                    vis.simplify(),
                    mutability.0,
                    name,
                    None,
                    Expr::dummy(),
                    Span::join(lo, hi),
                )),
        }
    }

    /// Parses a extern block item.
    pub fn parse_extern_item(
        &mut self,
        vis: Visibility<Span>,
        mutability: (Mutability, Option<Span>),
    ) -> ReResult<Item> {
        if let (Mutability::Mut, Some(mut_span)) = mutability {
            self.dcx
                .emit(MutQualifierNotPermitted { primary: mut_span });
        }

        if let Visibility::Public(vis_span) = vis {
            self.dcx
                .emit(VisQualifierNotPermitted { primary: vis_span });
        }

        let lo = tri!(self.expect(ExpToken::KwExtern));

        let lit_span = tri!(self.expect(ExpToken::Lit));
        let lit = self.as_lit();

        let strlit = if let Some(strlit) = lit.as_string() {
            strlit
        } else {
            self.dcx.emit(ExpectedToken::new(
                ["string literal"],
                self.prev_token.clone(),
            ));

            sym::Muon
        };

        let abi = match Abi::from_str(strlit.as_str()) {
            Ok(abi) => abi,
            Err(()) => {
                self.dcx.emit(InvalidAbi {
                    abi: strlit,
                    primary: lit_span,
                });
                Abi::Muon
            }
        };

        tri!(self.expect(ExpToken::LCurly));

        let items = tri!(self.parse_item_seq());

        let hi = tri!(self.expect(ExpToken::RCurly));

        Ok(Item::Extern(abi, items, Span::join(lo, hi)))
    }

    /// Parses a directive item.
    pub fn parse_directive_item(&mut self) -> ReResult<Item> {
        Ok(Item::Directive(tri!(self.parse_directive())))
    }
}
