//! Parsing of Muon's directives

use crate::diags::UnknownDirective;

use super::*;

/// Muon directive
#[derive(Debug, Clone)]
pub enum Directive {
    /// `"#" "mod" ident ";"`
    ModDecl(Identifier, Span),
    /// `"#" "mod" ident "{" item* "}"`
    ModDef(Identifier, Module, Span),
    /// `"#" "import" path ( "as" ident )? ";"`
    Import(Path, Option<Identifier>, Span),
}

impl Directive {
    /// List of the directives names.
    pub const DIRECTIVE_NAMES: &[Symbol] = &[sym::Mod, sym::Import];
}

impl Parser {
    /// Parses a directive
    pub fn parse_directive(&mut self) -> ReResult<Directive> {
        let tok = self.look_ahead(1, look_tok).clone();

        match tok.tt {
            Ident(sym::Mod) => self.parse_mod_directive(),
            Ident(sym::Import) => self.parse_import_directive(),
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
    pub fn parse_mod_directive(&mut self) -> ReResult<Directive> {
        let lo = tri!(self.expect(ExpToken::Pound));

        tri!(self.expect_weak_kw(WeakKw::Mod));

        tri!(self.expect(ExpToken::Ident));
        let name = self.as_ident();

        if self.eat(ExpToken::Semi) {
            let hi = self.token_span();

            Ok(Directive::ModDecl(name, Span::join(lo, hi)))
        } else if self.eat(ExpToken::LCurly) {
            let module = self.parse_module().dere_or(|| Module {
                items: vec![],
                fid: self.fid,
            });

            let hi = tri!(self.expect(ExpToken::RCurly));

            Ok(Directive::ModDef(name, module, Span::join(lo, hi)))
        } else {
            // failed, return the guarantee
            self.expdiag_bump(None)
        }
    }

    /// Parses an import directive
    pub fn parse_import_directive(&mut self) -> ReResult<Directive> {
        let lo = tri!(self.expect(ExpToken::Pound));

        tri!(self.expect_weak_kw(WeakKw::Import));

        let path = tri!(self.parse_path()).node;

        let alias = if self.eat_no_expect(ExpToken::KwAs) {
            tri!(self.expect(ExpToken::Ident));

            Some(self.as_ident())
        } else {
            None
        };

        let hi = tri!(self.expect(ExpToken::Semi));

        Ok(Directive::Import(path, alias, Span::join(lo, hi)))
    }
}
