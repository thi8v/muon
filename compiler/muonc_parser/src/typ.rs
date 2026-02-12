//! Parsing of Muon's types

use super::*;

/// A Muon type.
#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

/// A type kind.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    /// `path`
    Path(Path),
    /// `* "mut"? type`
    Pointer(Mutability, Box<Type>),
    /// `fun "(" ( type ),* ")" ( "->" type )?`
    Funptr(Vec<Type>, Option<Box<Type>>),
}

/// [`Type`] parsing.
impl Parser {
    /// Parses a type.
    pub fn parse_type(&mut self) -> ReResult<Type> {
        match self.token.tt {
            Ident(_) | Kw(Keyword::Pkg) => self.parse_path_type(),
            Star => self.parse_ptr_type(),
            Kw(Keyword::Fun) => self.parse_funptr_type(),
            _ => {
                self.bump();

                self.dcx
                    .emit(ExpectedToken::new(["type"], self.prev_token.clone()))
                    .cant_rec()
            }
        }
    }

    /// Parses a path type.
    pub fn parse_path_type(&mut self) -> ReResult<Type> {
        let path = tri!(self.parse_path());

        Ok(Type {
            kind: TypeKind::Path(path.node),
            span: path.span,
        })
    }

    /// Parses a pointer type.
    pub fn parse_ptr_type(&mut self) -> ReResult<Type> {
        let lo = tri!(self.expect(ExpToken::Star));

        let mutability = self.parse_mutability();

        let typ = Box::new(tri!(self.parse_type()));
        let hi = typ.span;

        Ok(Type {
            kind: TypeKind::Pointer(mutability, typ),
            span: Span::join(lo, hi),
        })
    }

    /// Parses a function pointer type.
    pub fn parse_funptr_type(&mut self) -> ReResult<Type> {
        let lo = tri!(self.expect(ExpToken::KwFun));

        let Spanned {
            node: params,
            span: hi_paren,
        } = tri!(self.parse_parenthesized(Parser::parse_type));

        let (hi, ret) = if self.eat_no_expect(ExpToken::MinusGt) {
            let typ = Box::new(tri!(self.parse_type()));

            (typ.span, Some(typ))
        } else {
            (hi_paren, None)
        };

        Ok(Type {
            kind: TypeKind::Funptr(params, ret),
            span: Span::join(lo, hi),
        })
    }
}
