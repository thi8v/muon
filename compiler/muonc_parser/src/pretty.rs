//! Pretty printing of the AST of Muon

use std::io::{self, Write};

use muonc_utils::{
    impl_pdump,
    pretty::{PrettyCtxt, PrettyDump},
    pretty_struct,
};

use crate::{
    ast::*,
    expr::{LabelDef, LabelUse},
};

impl<E> PrettyDump<E> for Module {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        ctx.pretty_list(None, extra)
            .items(self.items.iter())
            .finish()
    }
}

impl<E> PrettyDump<E> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            Item::Fundef(vis, name, sig, block, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Fundef",
                    {
                        vis,
                        name,
                        sig,
                        block,
                    },
                    span
                }

                Ok(())
            }
            Item::Fundecl(vis, name, sig, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Fundecl",
                    {
                        vis,
                        name,
                        sig,
                    },
                    span
                }

                Ok(())
            }
            Item::Globdef(vis, mutability, name, typ, expr, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Globdef",
                    {
                        vis,
                        mutability,
                        name,
                        typ,
                        expr
                    },
                    span
                }

                Ok(())
            }
            Item::Globdecl(vis, mutability, name, typ, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Globdecl",
                    {
                        vis,
                        mutability,
                        name,
                        typ,
                    },
                    span
                }

                Ok(())
            }
            Item::Extern(abi, items, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Extern",
                    {
                        abi,
                        items,
                    },
                    span
                }

                Ok(())
            }
            Item::Directive(directive) => directive.try_dump(ctx, extra),
        }
    }
}

impl<E> PrettyDump<E> for Directive {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            Directive::ModDecl(name, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "ModDecl",
                    {
                        name,
                    },
                    span
                }

                Ok(())
            }
            Directive::ModDef(name, Module { items, fid: _ }, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "ModDef",
                    {
                        name,
                        items,
                    },
                    span
                }

                Ok(())
            }
            Directive::Import(path, alias, span) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Import",
                    {
                        path,
                        alias,
                    },
                    span
                }

                Ok(())
            }
        }
    }
}

impl<E> PrettyDump<E> for Visibility {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &E) -> io::Result<()> {
        match self {
            Visibility::Public(()) => write!(ctx.out, "pub"),
            Visibility::Private => write!(ctx.out, "private"),
        }
    }
}

impl<E> PrettyDump<E> for Sig {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let Sig { params, ret, span } = self;

        pretty_struct! {
            ctx,
            extra,
            "Sig",
            {
                params,
                ret,
            },
            span
        }

        Ok(())
    }
}

impl<E> PrettyDump<E> for Block {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        struct Tail<'ast>(&'ast Option<Expr>);

        impl<'ast, E> PrettyDump<E> for Tail<'ast> {
            fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
                write!(ctx.out, "@last_expr: ")?;
                self.0.try_dump(ctx, extra)?;

                Ok(())
            }
        }

        let last = Tail(&self.tail);

        ctx.pretty_list(Some("Block".to_string()), extra)
            .items(self.stmts.iter())
            .item(last)
            .finish()?;

        ctx.print_span(&self.span)?;

        Ok(())
    }
}

impl<E> PrettyDump<E> for Expr {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        if cfg!(debug_assertions) && *self == Expr::dummy() {
            write!(ctx.out, "*DUMMY EXPRESSION*")
        } else {
            self.kind.try_dump(ctx, extra)?;
            ctx.print_span(&self.span)
        }
    }
}

impl<E> PrettyDump<E> for ExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            ExprKind::Bool(b) => write!(ctx.out, "bool {b}"),
            ExprKind::Lit(lit) => write!(ctx.out, "{lit}"),
            ExprKind::Paren(expr) => {
                write!(ctx.out, "Paren(")?;
                expr.try_dump(ctx, extra)?;
                write!(ctx.out, ")")?;

                Ok(())
            }
            ExprKind::Path(path) => write!(ctx.out, "path {path}"),
            ExprKind::Binary(lhs, binop, rhs) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Binary",
                    {
                        lhs,
                        binop,
                        rhs,
                    }
                }

                Ok(())
            }
            ExprKind::Unary(unop, expr) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Unary",
                    {
                        unop,
                        expr,
                    }
                }

                Ok(())
            }
            ExprKind::Borrow(mutability, expr) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Borrow",
                    {
                        mutability,
                        expr,
                    }
                }

                Ok(())
            }
            ExprKind::Call(callee, args) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Call",
                    {
                        callee,
                        args,
                    }
                }

                Ok(())
            }
            ExprKind::If(flavor, cond, then, r#else) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "If",
                    {
                        flavor,
                        cond,
                        then,
                        r#else,
                    }
                }

                Ok(())
            }
            ExprKind::Block(label, block) => {
                if label.0.is_some() {
                    pretty_struct! {
                        ctx,
                        extra,
                        "LabeledBlock",
                        {
                            label,
                            block,
                        }
                    }

                    Ok(())
                } else {
                    block.try_dump(ctx, extra)
                }
            }
            ExprKind::While(label, cond, block) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "While",
                    {
                        label,
                        cond,
                        block,
                    }
                }

                Ok(())
            }
            ExprKind::For(label, binding, iter, block) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "For",
                    {
                        label,
                        binding,
                        iter,
                        block,
                    }
                }

                Ok(())
            }
            ExprKind::Loop(label, block) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Loop",
                    {
                        label,
                        block
                    }
                }

                Ok(())
            }
            ExprKind::Return(expr) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Return",
                    {
                        expr,
                    }
                }

                Ok(())
            }
            ExprKind::Break(label, expr) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Break",
                    {
                        label,
                        expr,
                    }
                }

                Ok(())
            }
            ExprKind::Continue(label) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Continue",
                    {
                        label,
                    }
                }

                Ok(())
            }
            ExprKind::Field(operand, member) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Field",
                    {
                        operand,
                        member,
                    }
                }

                Ok(())
            }
            ExprKind::Cast(operand, typ) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Cast",
                    {
                        operand,
                        typ,
                    }
                }

                Ok(())
            }
        }
    }
}

impl<E> PrettyDump<E> for LabelDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let LabelDef(spanned_ident) = self;

        spanned_ident.try_dump(ctx, extra)
    }
}

impl<E> PrettyDump<E> for LabelUse {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let LabelUse(spanned_ident) = self;

        spanned_ident.try_dump(ctx, extra)
    }
}

impl_pdump! {
    IfFlavor
}

impl<E> PrettyDump<E> for Stmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.kind.try_dump(ctx, extra)?;
        ctx.print_span(&self.span)
    }
}

impl<E> PrettyDump<E> for StmtKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            StmtKind::BindingDef(mutability, name, typ, val) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "BindingDef",
                    {
                        mutability,
                        name,
                        typ,
                        val,
                    },
                };

                Ok(())
            }
            StmtKind::Expr(expr) => expr.try_dump(ctx, extra),
        }
    }
}

impl<E> PrettyDump<E> for Param {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        let Param { name, typ, span } = self;

        pretty_struct! {
            ctx,
            extra,
            "Param",
            {
                name,
                typ,
            },
            span
        }

        Ok(())
    }
}

impl<E> PrettyDump<E> for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        self.kind.try_dump(ctx, extra)?;
        ctx.print_span(&self.span)?;

        Ok(())
    }
}

impl<E> PrettyDump<E> for TypeKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &E) -> io::Result<()> {
        match self {
            TypeKind::Path(path) => path.try_dump(ctx, extra),
            TypeKind::Pointer(mutability, typ) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Pointer",
                    {
                        mutability,
                        typ,
                    }
                }

                Ok(())
            }

            TypeKind::Funptr(params, ret) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Funptr",
                    {
                        params,
                        ret
                    }
                }

                Ok(())
            }
        }
    }
}
