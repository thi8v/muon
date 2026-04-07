//! Parsing of Muon's items

use std::str::FromStr;

use crate::diags::{InvalidAbi, MutQualifierNotPermitted};

use super::*;

/// Muon module, a collection of [`Item`]s that may be in a file or in a module
/// directive.
#[derive(Debug, Clone, PartialEq)]
pub struct Mod {
    /// The contained items.
    pub items: Vec<Item>,
    /// Inner span of the module, the span from the first token to the last
    /// token inside of the module (does not include the `{` `}` for `ModDef`).
    pub span: Span,
}

/// Function definition
///
/// *NB: the first span is the span from `fun` to `)` and the last span is
/// the span of the entire item.*
///
/// `ident "::" "fun" "(" ( ident ":" type ),* ")" ( "->" type )? block`
#[derive(Debug, Clone, PartialEq)]
pub struct Fundef {
    pub name: Identifier,
    pub sig: Sig,
    pub block: Block,
    pub span: Span,
}

/// Function declaration
///
/// *NB: the first span is the span from `fun` to `)` and the last span is
/// the span of the entire item.*
///
/// `ident "::" "fun" "(" ( ident ":" type ),* ")" ( "->" type )? ";"`
#[derive(Debug, Clone, PartialEq)]
pub struct Fundecl {
    pub name: Identifier,
    pub sig: Sig,
    pub span: Span,
}

/// Global definition
///
/// `"mut"? ident ":" (type)? "=" expr ";"`
#[derive(Debug, Clone, PartialEq)]
pub struct Globdef {
    pub mutability: Mutability,
    pub name: Identifier,
    pub ty: Option<Type>,
    pub expr: Expr,
    pub span: Span,
}

/// Global declaration
///
/// `"mut"? ident ":" type ";"`
#[derive(Debug, Clone, PartialEq)]
pub struct Globdecl {
    pub mutability: Mutability,
    pub name: Identifier,
    pub ty: Type,
    pub span: Span,
}

/// Extern block
///
/// `"extern" strlit "{" item* "}"`
#[derive(Debug, Clone, PartialEq)]
pub struct Extern {
    pub abi: Abi,
    pub items: Vec<Item>,
    pub span: Span,
}

/// Muon item
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// Function definition
    Fundef(Fundef),
    /// Function declaration
    Fundecl(Fundecl),
    /// Global definition
    Globdef(Globdef),
    /// Global declaration
    Globdecl(Globdecl),
    /// Extern block
    Extern(Extern),
    /// Directive
    Directive(Directive),
}

/// Function definition parameter
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Identifier,
    pub ty: Type,
    pub span: Span,
}

/// Function definition / declaration signature
#[derive(Debug, Clone, PartialEq)]
pub struct Sig {
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub span: Span,
}

/// [`Item`] and [`Mod`] parsing
impl Parser {
    /// Parses a module
    pub fn parse_module(&mut self) -> ReResult<Mod> {
        let lo = self.token.span;
        let items = tri!(self.parse_item_seq());
        let hi = self.token_span();

        Ok(Mod {
            items,
            span: Span::join(lo, hi),
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
        let mutability = self.parse_mutability();
        let mutability = (mutability, mutability.is_mut().then(|| self.token_span()));

        match self.token.tt {
            Ident(_) if self.look_ahead(1, |tok| matches!(tok.tt, ColonColon)) => {
                self.parse_fun_item(mutability)
            }
            Ident(_) if self.is_glob() => self.parse_glob_item(mutability),
            Kw(Keyword::Extern) => self.parse_extern_item(mutability),
            Pound => self.parse_directive_item(mutability),
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

        let ty = tri!(self.parse_type());
        let hi = ty.span;

        Ok(Param {
            name,
            ty,
            span: Span::join(lo, hi),
        })
    }

    /// Parses a fundef/fundecl item.
    pub fn parse_fun_item(&mut self, mutability: (Mutability, Option<Span>)) -> ReResult<Item> {
        if let (Mutability::Mut, Some(mut_span)) = mutability {
            self.dcx
                .emit(MutQualifierNotPermitted { primary: mut_span });
        }

        let lo = tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

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

            Ok(Item::Fundef(Fundef {
                name,
                sig,
                block,
                span: Span::join(lo, hi),
            }))
        } else if self.check(ExpToken::Semi) {
            let hi = tri!(self.expect(ExpToken::Semi));

            Ok(Item::Fundecl(Fundecl {
                name,
                sig,
                span: Span::join(lo, hi),
            }))
        } else {
            let span = Span::join(lo, sig.span);

            // NB: return a dumb item
            self.expdiag_bump(Item::Fundecl(Fundecl { name, sig, span }))
        }
    }

    /// Parses a globdef/globdecl item.
    pub fn parse_glob_item(&mut self, mutability: (Mutability, Option<Span>)) -> ReResult<Item> {
        let name_span = tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        let lo = mutability.1.unwrap_or(name_span);

        self.expect(ExpToken::Colon).discard();

        let (ty, expr) = if self.eat_no_expect(ExpToken::Eq) {
            (None, Some(tri!(self.parse_expr())))
        } else {
            let ty = tri!(self.parse_type());

            let expr = if self.eat_no_expect(ExpToken::Eq) {
                Some(tri!(self.parse_expr()))
            } else {
                None
            };

            (Some(ty), expr)
        };

        let hi = tri!(self.expect(ExpToken::Semi));

        match (ty, expr) {
            (ty, Some(expr)) => Ok(Item::Globdef(Globdef {
                mutability: mutability.0,
                name,
                ty,
                expr,
                span: Span::join(lo, hi),
            })),
            (Some(ty), None) => Ok(Item::Globdecl(Globdecl {
                mutability: mutability.0,
                name,
                ty,
                span: Span::join(lo, hi),
            })),
            (None, None) => unreachable!(),
        }
    }

    /// Parses a extern block item.
    pub fn parse_extern_item(&mut self, mutability: (Mutability, Option<Span>)) -> ReResult<Item> {
        if let (Mutability::Mut, Some(mut_span)) = mutability {
            self.dcx
                .emit(MutQualifierNotPermitted { primary: mut_span });
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

        Ok(Item::Extern(Extern {
            abi,
            items,
            span: Span::join(lo, hi),
        }))
    }

    /// Parses a directive item.
    pub fn parse_directive_item(
        &mut self,
        mutability: (Mutability, Option<Span>),
    ) -> ReResult<Item> {
        if let (Mutability::Mut, Some(mut_span)) = mutability {
            self.dcx
                .emit(MutQualifierNotPermitted { primary: mut_span });
        }

        Ok(Item::Directive(tri!(self.parse_directive())))
    }
}
