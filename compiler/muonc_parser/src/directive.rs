//! Parsing of Muon's directives

use crate::diags::UnknownDirective;

use super::*;

/// Module definition
///
/// *Allowed in: Item*
///
/// `vis? "#" "mod" ident "{" item* "}"`
#[derive(Debug, Clone, PartialEq)]
pub struct ModDef {
    pub vis: Visibility,
    pub name: Identifier,
    pub module: Mod,
    pub span: Span,
}

/// Module declaration
///
/// *Allowed in: Item*
///
/// `vis? "#" "mod" ident ";"`
#[derive(Debug, Clone, PartialEq)]
pub struct ModDecl {
    pub vis: Visibility,
    pub name: Identifier,
    pub span: Span,
}

/// Import
///
/// *Allowed in: Item, Stmt*
///
/// `vis? "#" "import" path ( "as" ident )? ";"`
#[derive(Debug, Clone, PartialEq)]
pub struct Import {
    pub vis: Visibility,
    pub path: Path,
    pub alias: Option<Identifier>,
    pub span: Span,
}

/// Muon directive
#[derive(Debug, Clone, PartialEq)]
pub enum Directive {
    /// Module declaration
    ModDecl(ModDecl),
    /// Module definition
    ModDef(ModDef),
    /// Import
    Import(Import),
}

impl Directive {
    /// List of the directives names.
    pub const DIRECTIVE_NAMES: &[Symbol] = &[sym::Mod, sym::Import];

    pub fn span(&self) -> Span {
        match self {
            Directive::ModDecl(ModDecl { span, .. })
            | Directive::ModDef(ModDef { span, .. })
            | Directive::Import(Import { span, .. }) => *span,
        }
    }
}

impl Parser {
    /// Parses a directive
    pub fn parse_directive(&mut self, vis: Visibility<Span>) -> ReResult<Directive> {
        let tok = self.look_ahead(1, look_tok).clone();

        match tok.tt {
            Ident(sym::Mod) => self.parse_mod_directive(vis),
            Ident(sym::Import) => self.parse_import_directive(vis),
            Ident(name) => {
                self.bump(); // '#'
                self.bump(); // the ident

                self.dcx
                    .emit(UnknownDirective {
                        name,
                        primary: Span::join(self.prev_token.span, tok.span),
                    })
                    .cant_rec()
            }
            _ => {
                tri!(self.expect(ExpToken::Pound));
                tri!(self.expect(ExpToken::Ident));

                // NB: we just checked before that ti + 1 isn't an identifier so
                // we are sure that we will return before that.
                unreachable!()
            }
        }
    }

    /// Parses a module directive
    pub fn parse_mod_directive(&mut self, vis: Visibility<Span>) -> ReResult<Directive> {
        let lo_pound = tri!(self.expect(ExpToken::Pound));
        let lo = vis.as_val().copied().unwrap_or(lo_pound);

        tri!(self.expect_weak_kw(WeakKw::Mod));

        tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        if self.eat(ExpToken::Semi) {
            let hi = self.token_span();

            Ok(Directive::ModDecl(ModDecl {
                vis: vis.simplify(),
                name,
                span: Span::join(lo, hi),
            }))
        } else if self.eat(ExpToken::LCurly) {
            let module = self.parse_module().dere_or(|| Mod {
                items: vec![],
                span: DUMMY_SP,
            });

            let hi = tri!(self.expect(ExpToken::RCurly));

            Ok(Directive::ModDef(ModDef {
                vis: vis.simplify(),
                name,
                module,
                span: Span::join(lo, hi),
            }))
        } else {
            // failed, return the guarantee
            self.expdiag_bump(None)
        }
    }

    /// Parses an import directive
    pub fn parse_import_directive(&mut self, vis: Visibility<Span>) -> ReResult<Directive> {
        let lo_pound = tri!(self.expect(ExpToken::Pound));
        let lo = vis.as_val().copied().unwrap_or(lo_pound);

        tri!(self.expect_weak_kw(WeakKw::Import));

        let path = tri!(self.parse_path()).node;

        let alias = if self.eat_no_expect(ExpToken::KwAs) {
            tri!(self.expect(ExpToken::Ident));

            Some(self.as_ident())
        } else {
            None
        };

        let hi = tri!(self.expect(ExpToken::Semi));

        Ok(Directive::Import(Import {
            vis: vis.simplify(),
            path,
            alias,
            span: Span::join(lo, hi),
        }))
    }
}
