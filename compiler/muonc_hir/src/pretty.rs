//! Pretty printing of the HIR in a tree-like form.

use std::io::{self, Write};

use muonc_entity::Entity;
use muonc_span::def_id::DefId;
use muonc_utils::{
    pretty::{PrettyCtxt, PrettyDump},
    pretty_struct,
};

use crate::hir::{BindingDef, *};

/// Used for the `PrettyDump` implementation of HIR.
#[derive(Debug, Clone, Copy)]
pub struct PkgDumper;

impl PrettyDump<PkgDumper> for Package {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Package {
            owners,
            generated,
            traces,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Package",
            {
                owners: ctx.pretty_map(owners.full_iter(), extra)?,
                generated: ctx.pretty_map(generated.iter(), extra)?,
                traces: ctx.pretty_map(traces.full_iter(), extra)?,
            }
        };

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for GenId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "gen{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for DefId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "def{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for BlockId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "blk{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for PathSegmentId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "seg{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for ExprId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "e{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for LabelId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "l{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for StmtId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "s{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for TyId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "ty{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for ParamId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "param{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for PathId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "path{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for LocalId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "local{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for BindingId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "bind{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for ExternHeaderId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "ext{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for ResId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "res{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for ItemId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        self.0.try_dump(ctx, extra)
    }
}

impl PrettyDump<PkgDumper> for NodeId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "n{}", self.index())
    }
}

impl PrettyDump<PkgDumper> for OwnerId {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "o{}", self.index())
    }
}

impl<Id: NodeType + PrettyDump<PkgDumper>> PrettyDump<PkgDumper> for HirId<Id> {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let HirId { owner, node_id } = self;

        node_id.try_dump(ctx, extra)?;
        write!(ctx.out, "@")?;
        owner.try_dump(ctx, extra)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for GenTrace {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}

impl PrettyDump<PkgDumper> for MaybeOwner {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            MaybeOwner::Owner(owner) => owner.try_dump(ctx, extra),
            MaybeOwner::NonOwner(hir_id) => hir_id.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<PkgDumper> for NodeOwner {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let NodeOwner { nodes } = self;

        write!(ctx.out, "Owner ")?;
        ctx.pretty_map(nodes.full_iter(), extra)
    }
}

impl PrettyDump<PkgDumper> for Node {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            Node::Package(Mod { items, .. }) => ctx
                .pretty_list(Some("Package"), extra)
                .disable_nl()
                .items(items)
                .finish(),
            Node::Item(item) => item.try_dump(ctx, extra),
            Node::Param(param) => param.try_dump(ctx, extra),
            Node::Type(ty) => ty.try_dump(ctx, extra),
            Node::Block(block) => block.try_dump(ctx, extra),
            Node::Stmt(stmt) => stmt.try_dump(ctx, extra),
            Node::Expr(expr) => expr.try_dump(ctx, extra),
            Node::PathSegment(pathseg) => pathseg.try_dump(ctx, extra),
            Node::Label(label) => label.try_dump(ctx, extra),
            Node::BindingDef(binddef) => binddef.try_dump(ctx, extra),
            Node::Local(local) => local.try_dump(ctx, extra),
            Node::Path(path) => path.try_dump(ctx, extra),
            Node::ExternHeader(ext) => ext.try_dump(ctx, extra),
            Node::Res(res) => res.try_dump(ctx, extra),
            Node::Reserved(kind, span) => {
                write!(ctx.out, "RESERVED({kind:?})")?;
                ctx.print_span(span)?;

                Ok(())
            }
        }
    }
}

impl PrettyDump<PkgDumper> for Item {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Item { kind, span } = self;

        kind.try_dump(ctx, extra)?;
        ctx.print_span(span)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for ItemKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            ItemKind::Fundef(fundef) => fundef.try_dump(ctx, extra),
            ItemKind::Fundecl(fundecl) => fundecl.try_dump(ctx, extra),
            ItemKind::Globdef(globdef) => globdef.try_dump(ctx, extra),
            ItemKind::Globdecl(globdecl) => globdecl.try_dump(ctx, extra),
            ItemKind::Directive(directive) => directive.try_dump(ctx, extra),
        }
    }
}

impl PrettyDump<PkgDumper> for Fundef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Fundef {
            abi,
            name,
            sig,
            body,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Fundef",
            {
                abi,
                name,
                sig,
                body,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Sig {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
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

impl PrettyDump<PkgDumper> for Fundecl {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Fundecl { ext, name, sig } = self;

        pretty_struct! {
            ctx,
            extra,
            "Fundecl",
            {
                ext,
                name,
                sig,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Globdef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Globdef {
            mutability,
            name,
            ty,
            expr,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Globdef",
            {
                mutability,
                name,
                ty,
                expr,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Globdecl {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Globdecl {
            ext,
            mutability,
            name,
            ty,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Globdecl",
            {
                ext,
                mutability,
                name,
                ty,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for ExternHeader {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let ExternHeader {
            abi,
            span,
            block_span,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "ExternHeader",
            {
                abi,
                block_span,
            },
            span
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Directive {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            Directive::Mod(name, module) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Directive::Mod",
                    {
                        name,
                        module,
                    }
                }

                Ok(())
            }
            Directive::Import { path, alias } => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Directive::Import",
                    {
                        path,
                        alias,
                    }
                }

                Ok(())
            }
        }
    }
}

impl PrettyDump<PkgDumper> for Mod {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Mod { items, span } = self;

        ctx.pretty_list(Some("Mod"), extra)
            .items(items)
            .disable_nl()
            .finish()?;
        ctx.print_span(span)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Path {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Path {
            res,
            segments,
            span,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Path",
            {
                res,
                segments,
            },
            span
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Res {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            Res::Def(kind, defid) => {
                write!(ctx.out, "{kind} @ ")?;
                defid.try_dump(ctx, extra)?;

                Ok(())
            }
            Res::PrimTy(primty) => {
                write!(ctx.out, "primty({})", primty.to_symbol())
            }
            Res::Local(hirid) => {
                write!(ctx.out, "local @ ")?;
                hirid.try_dump(ctx, extra)
            }
            Res::Unresolved => {
                write!(ctx.out, "/* UNRESOLVED */")
            }
        }
    }
}

impl PrettyDump<PkgDumper> for Param {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Param {
            name,
            ty,
            span,
            local,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Param",
            {
                name,
                ty,
                local,
            },
            span
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Type {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Type { kind, span } = self;

        kind.try_dump(ctx, extra)?;
        ctx.print_span(span)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for TypeKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            TypeKind::Path(path) => path.try_dump(ctx, extra),
            TypeKind::Pointer(mutability, pointee) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Pointer",
                    {
                        mutability,
                        pointee,
                    }
                }

                Ok(())
            }
            TypeKind::Funptr(args, ret) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Funptr",
                    {
                        args,
                        ret,
                    }
                }

                Ok(())
            }
        }
    }
}

impl PrettyDump<PkgDumper> for Block {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Block { stmts, tail, span } = self;

        pretty_struct! {
            ctx,
            extra,
            "Block",
            {
                stmts,
                tail,
            },
            span
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Stmt {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Stmt { kind, span } = self;

        kind.try_dump(ctx, extra)?;
        ctx.print_span(span)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for StmtKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "stmt(")?;

        match self {
            StmtKind::BindingDef(bind_id) => {
                bind_id.try_dump(ctx, extra)?;
            }
            StmtKind::Directive(id) => {
                id.try_dump(ctx, extra)?;
            }
            StmtKind::Expr(expr) => {
                write!(ctx.out, "expr: ")?;
                expr.try_dump(ctx, extra)?;
            }
            StmtKind::Semi(expr) => {
                write!(ctx.out, "semi: ")?;
                expr.try_dump(ctx, extra)?;
            }
        }

        write!(ctx.out, ")")?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Expr {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Expr { kind, span } = self;

        kind.try_dump(ctx, extra)?;
        ctx.print_span(span)?;

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for ExprKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        match self {
            ExprKind::Bool(bool) => write!(ctx.out, "bool {bool}"),
            ExprKind::Lit(lit) => write!(ctx.out, "{lit}"),
            ExprKind::Path(path) => path.try_dump(ctx, extra),
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
            ExprKind::If(cond, then, els) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "If",
                    {
                        cond,
                        then,
                        els,
                    }
                }

                Ok(())
            }
            ExprKind::Block(label, block) => {
                block.try_dump(ctx, extra)?;

                if let Some(label) = label.expand() {
                    write!(ctx.out, " @ ")?;
                    label.try_dump(ctx, extra)?;
                }

                Ok(())
            }
            ExprKind::Loop(label, body) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Loop",
                    {
                        label,
                        body,
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
            ExprKind::Field(op, member) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Field",
                    {
                        op,
                        member,
                    }
                }

                Ok(())
            }
            ExprKind::Cast(expr, ty) => {
                pretty_struct! {
                    ctx,
                    extra,
                    "Cast",
                    {
                        expr,
                        ty,
                    }
                }

                Ok(())
            }
        }
    }
}

impl PrettyDump<PkgDumper> for PathSegment {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let PathSegment { ident, id, res } = self;

        pretty_struct! {
            ctx,
            extra,
            "PathSegment",
            {
                ident,
                id,
                res,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Label {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Label {
            id,
            def,
            name,
            kind,
            breaked,
        } = self;

        pretty_struct! {
            ctx,
            extra,
            "Label",
            {
                id,
                def,
                name,
                kind,
                breaked,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for LabelKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        match self {
            LabelKind::Block => write!(ctx.out, "Block"),
            LabelKind::While => write!(ctx.out, "While"),
            LabelKind::Loop => write!(ctx.out, "Loop"),
        }
    }
}

impl PrettyDump<PkgDumper> for BindingDef {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let BindingDef(mutability, name, ty, expr, local, span) = self;

        pretty_struct! {
            ctx,
            extra,
            "BindingDef",
            {
                mutability,
                name,
                ty,
                expr,
                local,
            },
            span
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for Local {
    fn try_dump(&self, ctx: &mut PrettyCtxt, extra: &PkgDumper) -> io::Result<()> {
        let Local { name, kind, def } = self;

        pretty_struct! {
            ctx,
            extra,
            "Local",
            {
                name,
                kind,
                def,
            }
        }

        Ok(())
    }
}

impl PrettyDump<PkgDumper> for LocalKind {
    fn try_dump(&self, ctx: &mut PrettyCtxt, _: &PkgDumper) -> io::Result<()> {
        write!(ctx.out, "{self:?}")
    }
}
