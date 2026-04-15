//! Lowering of AST to HIR.

use std::{mem, path::PathBuf, sync::Arc};

use muonc_entity::{Entity, EntityMap, Opt};
use muonc_errors::{FeatureNotImplemented, prelude::*};
use muonc_lexer::Lexer;
use muonc_middle::{
    ast::{Abi, UnOp},
    session::Session,
};
use muonc_parser::{Parser, ast};
use muonc_span::prelude::*;
use muonc_token::{Lit, TokenStream};

use crate::{
    diags::{
        BreakWithValueUnsupported, CannotNestExternBlocks, CantContinueABlock,
        LabelKwOutsideLoopOrBlock, ModuleFilePathErr, UseOfUndefinedLabel, WLabelShadowed,
    },
    hir::{
        self, BindingDef, BindingId, BlockId, ExprId, ExternHeaderId, GenId, GenTrace, HirId,
        ItemId, LabelId, LocalId, LocalKind, MaybeOwner, NodeId, NodeOwner, NodeType, OwnerId,
        ParamId, PathId, PathSegmentId, ResId, StmtId, TyId,
    },
};

/// Lowering all of the AST to HIR, we mark paths as *unresolved* at this stage,
/// (`lower_` methods)
#[derive(Debug)]
pub struct LoweringCtx {
    /// the package we are compiling
    pub(crate) pkg: hir::Package,
    /// the current owner
    pub(crate) cursor: OwnerId,
    /// label stack, **item specific**
    pub(crate) label_stack: Vec<hir::LabelId>,
    /// the parser, used for lowering of module declaration, instead of
    /// recrating one each time.
    pub parser: Parser,
    /// current extern header block id.
    pub(crate) cur_ext: Opt<ExternHeaderId>,
    /// diagnostic context
    pub(crate) dcx: DiagCtxt,
    /// compilation session
    pub(crate) session: Arc<Session>,
}

impl LoweringCtx {
    /// Create a new HIR Context.
    pub fn new(session: Arc<Session>) -> LoweringCtx {
        LoweringCtx {
            pkg: hir::Package::new(),
            cursor: OwnerId::from(DefId::PACKAGE_DEF),
            label_stack: Vec::new(),
            parser: Parser::new_empty(session.clone()),
            cur_ext: Opt::None,
            dcx: session.dcx.clone(),
            session,
        }
    }

    /// Produce an HIR Package from the Ast root module.
    pub fn produce(&mut self, ast_root: ast::Mod) -> ReResult<hir::Package> {
        // create the (special) root mod of the package.
        let root = self.mk_package(ast_root.span);

        debug_assert_eq!(
            root.0,
            DefId::PACKAGE_DEF,
            "DefId(0) must be the package's root."
        );

        // lower the AST items to HIR.
        self.lower_item_seq(&ast_root.items, root);

        let pkg = mem::take(&mut self.pkg);

        if self.dcx.failed() {
            return Err(Recovered::Yes(pkg, self.dcx.has_emitted().unwrap()));
        }

        Ok(pkg)
    }

    // Package helper methods

    /// Get a reference to the owner from its id.
    pub fn get_owner(&self, owner_id: OwnerId) -> &NodeOwner {
        self.pkg.owners.get(owner_id.0).unwrap()
    }

    /// Mutable `LoweringCtx::get_owner`.
    pub fn mut_owner(&mut self, owner_id: OwnerId) -> &mut NodeOwner {
        self.pkg.owners.get_mut(owner_id.0).unwrap_mut()
    }

    /// Get a node from the given HIR Id
    pub fn get_hirid(&self, hir_id: HirId) -> &hir::Node {
        self.get_owner(hir_id.owner).nodes.get(hir_id.node_id)
    }

    /// Get a reference to the `NodeOwner` of the `HirCtx::cursor`
    pub fn cur(&self) -> &NodeOwner {
        self.get_owner(self.cursor)
    }

    /// Mutable `HirCtx::cur`
    pub fn mut_cur(&mut self) -> &mut NodeOwner {
        self.mut_owner(self.cursor)
    }

    /// Get the HIR Id of the current node with the cursor being the owner.
    pub fn hir_id(&self, node_id: NodeId) -> HirId {
        HirId {
            owner: self.cursor,
            node_id,
        }
    }

    // Reset methods

    /// Reset the item-specific parts of the Hir context.
    pub fn reset_item_specific(&mut self) {
        self.label_stack.clear()
    }
}

/// Node accessors, access a node in the current owner (`Self::cursor`).
impl LoweringCtx {
    /// Get the node with the given id.
    #[must_use]
    pub fn get_node(&self, node_id: NodeId) -> &hir::Node {
        self.cur().nodes.get(node_id)
    }

    /// Mutable `get_node`.
    #[must_use]
    pub fn mut_node(&mut self, node_id: NodeId) -> &mut hir::Node {
        self.mut_cur().nodes.get_mut(node_id)
    }

    /// Get the label at the given id, panics if it's not a label.
    ///
    /// *NB: if `check` is set to true, the function will check if the provided
    /// label is in the stack, will panic if true and not present in the stack.*
    #[must_use]
    pub fn get_label(&self, label: LabelId, check: bool) -> &hir::Label {
        if check && !self.label_stack.contains(&label) {
            panic!("this label isn't in the stack.")
        }

        match self.get_node(label.0) {
            hir::Node::Label(label) => label,
            _ => panic!("{} is not a label.", self.hir_id(label.0)),
        }
    }

    /// Mutable `get_label`
    #[must_use]
    pub fn mut_label(&mut self, label: LabelId, check: bool) -> &mut hir::Label {
        if check && !self.label_stack.contains(&label) {
            panic!("this label isn't in the stack.")
        }

        let hir_id = self.hir_id(label.0);

        match self.mut_node(label.0) {
            hir::Node::Label(label) => label,
            _ => panic!("{} is not a label.", hir_id),
        }
    }
}

/// Make HIR Nodes Methods
///
/// *NB: every `mk_` and `reserve_` methods that return a `NodeId` or an
/// alias type (like `BlockId`, `TyId`, `ExprId`, etc.) is local to the cursor
/// (`HirCtx::cursor`) and if the node created owns items it will create the
/// owner.*
impl LoweringCtx {
    /// Make a new owner (don't move the cursor, and contains no nodes).
    #[must_use]
    pub fn mk_owner(&mut self, def: hir::Item) -> OwnerId {
        let mut nodes = EntityMap::new();
        nodes.create(hir::Node::Item(def));

        OwnerId::from(
            self.pkg
                .owners
                .create(MaybeOwner::Owner(NodeOwner { nodes })),
        )
    }

    /// Make a `Node`.
    #[must_use]
    pub fn mk_node(&mut self, node: hir::Node) -> NodeId {
        self.mut_cur().nodes.create(node)
    }

    /// Make multiple nodes with one constructor.
    #[must_use]
    pub fn mk_node_many<const N: usize>(
        &mut self,
        ctor: impl FnOnce([NodeId; N]) -> [hir::Node; N],
    ) -> [NodeId; N] {
        self.mut_cur().nodes.create_many_once(ctor)
    }

    /// Make a `Node` with the given closure.
    #[must_use]
    pub fn mk_node_with(&mut self, ctor: impl FnOnce(NodeId) -> hir::Node) -> NodeId {
        self.mut_cur().nodes.create_with(ctor)
    }

    /// Make an `Item`.
    #[must_use]
    pub fn mk_item(&mut self, kind: hir::ItemKind, span: Span) -> ItemId {
        let item = hir::Item { kind, span };
        let owner = item.kind.can_own();

        let item_id = if owner {
            let owner_id = self.mk_owner(item);

            ItemId::from(owner_id.0)
        } else {
            let node = self.mk_node(hir::Node::Item(item));
            let hir_id = self.hir_id(node);

            ItemId::from(self.pkg.owners.create(MaybeOwner::NonOwner(hir_id)))
        };

        self.mut_cur().push_items(item_id);

        item_id
    }

    /// Make **the only** `Node::Package`.
    #[must_use]
    pub fn mk_package(&mut self, span: Span) -> OwnerId {
        debug_assert!(
            span.fid.is_root(),
            "you must provide the ast of the package root."
        );

        let mut nodes = EntityMap::new();
        nodes.create(hir::Node::Package(hir::Mod {
            items: vec![],
            span,
        }));

        OwnerId::from(
            self.pkg
                .owners
                .create(MaybeOwner::Owner(NodeOwner { nodes })),
        )
    }

    /// Make a `Node::Block`.
    pub fn mk_block(&mut self, stmts: Vec<hir::StmtId>, tail: Opt<ExprId>, span: Span) -> BlockId {
        self.mk_node(hir::Node::Block(hir::Block { stmts, tail, span }))
            .to_block_id()
    }

    /// Make a `Node::PathSegment`.
    #[must_use]
    pub fn mk_path_segment(&mut self, ident: Identifier, res: HirId<ResId>) -> PathSegmentId {
        self.mk_node_with(|node_id| {
            hir::Node::PathSegment(hir::PathSegment {
                ident,
                id: node_id.to_path_segment_id(),
                res,
            })
        })
        .to_path_segment_id()
    }

    /// Make a `Node::Local`.
    #[must_use]
    pub fn mk_local(&mut self, local: hir::Local) -> LocalId {
        self.mk_node(hir::Node::Local(local)).to_local_id()
    }

    /// Make a `Node::Param`.
    #[must_use]
    pub fn mk_param(&mut self, name: Identifier, ty: TyId, span: Span) -> ParamId {
        self.mk_node_many(|[local_id, param_id]| {
            let local = hir::Node::Local(hir::Local {
                name,
                kind: LocalKind::Param,
                def: param_id,
            });

            let param = hir::Node::Param(hir::Param {
                name,
                ty,
                span,
                local: local_id.to_local_id(),
            });

            [local, param]
        })[1]
            .to_param_id()
    }

    /// Make a `Node::Type`.
    #[must_use]
    pub fn mk_type(&mut self, kind: hir::TypeKind, span: Span) -> TyId {
        self.mk_node(hir::Node::Type(hir::Type { kind, span }))
            .to_ty_id()
    }

    /// Make a `Node::Stmt`.
    #[must_use]
    pub fn mk_stmt(&mut self, kind: hir::StmtKind, span: Span) -> StmtId {
        self.mk_node(hir::Node::Stmt(hir::Stmt { kind, span }))
            .to_stmt_id()
    }

    /// Make a `Node::Expr`.
    #[must_use]
    pub fn mk_expr(&mut self, kind: hir::ExprKind, span: Span) -> ExprId {
        self.mk_node(hir::Node::Expr(hir::Expr { kind, span }))
            .to_expr_id()
    }

    /// Make a `Node::Path`.
    #[must_use]
    pub fn mk_path(&mut self, path: hir::Path) -> PathId {
        self.mk_node(hir::Node::Path(path)).to_path_id()
    }

    /// Make a `Node::Res`.
    #[must_use]
    pub fn mk_res(&mut self, res: hir::Res) -> HirId<ResId> {
        HirId {
            owner: self.cursor,
            node_id: self.mk_node(hir::Node::Res(res)).to_res_id(),
        }
    }

    /// Reserve a `Node::Expr`.
    #[must_use]
    pub fn reserve_expr(&mut self, span: Span) -> ExprId {
        self.mk_node(hir::Node::Reserved(hir::ReservationKind::Expr, span))
            .to_expr_id()
    }

    /// Reserve a `Node::Stmt`.
    #[must_use]
    pub fn reserve_stmt(&mut self, span: Span) -> StmtId {
        self.mk_node(hir::Node::Reserved(hir::ReservationKind::Stmt, span))
            .to_stmt_id()
    }

    /// Populate a reserved expression.
    pub fn pop_expr(&mut self, expr: ExprId, kind: hir::ExprKind) {
        let span = self.get_node(expr.0).span();

        debug_assert!(
            self.get_node(expr.0)
                .is_reserved(hir::ReservationKind::Expr),
            "can only populate a node that is marked as reserved"
        );

        *self.mut_node(expr.0) = hir::Node::Expr(hir::Expr { kind, span });
    }

    /// Populate a reserved statement.
    pub fn pop_stmt(&mut self, stmt: StmtId, kind: hir::StmtKind) {
        let span = self.get_node(stmt.0).span();

        debug_assert!(
            self.get_node(stmt.0)
                .is_reserved(hir::ReservationKind::Stmt),
            "can only populate a node that is marked as reserved"
        );

        *self.mut_node(stmt.0) = hir::Node::Stmt(hir::Stmt { kind, span });
    }

    /// Free the provided reserved node.
    pub fn free_reserved<Id: NodeType>(&mut self, node: Id) -> Option<hir::Node> {
        let node = node.into();

        debug_assert!(matches!(self.get_node(node), hir::Node::Reserved(..)));

        self.mut_cur().nodes.try_remove(node)
    }

    /// `mk_expr` but with access to the expr id.
    #[must_use]
    pub fn mk_expr_with(
        &mut self,
        kind: impl FnOnce(ExprId) -> hir::ExprKind,
        span: Span,
    ) -> ExprId {
        self.mk_node_with(|id| {
            hir::Node::Expr(hir::Expr {
                kind: kind(id.to_expr_id()),
                span,
            })
        })
        .to_expr_id()
    }

    /// Make a `Node::Label`.
    ///
    /// *NB: this function will not push this label on top of the stack, use
    /// `bind_label` instead.*
    #[must_use]
    pub fn mk_label(
        &mut self,
        name: Option<Spanned<Identifier>>,
        kind: hir::LabelKind,
        def: ExprId,
    ) -> LabelId {
        self.mk_node_with(|node_id| {
            hir::Node::Label(hir::Label {
                id: LabelId(node_id),
                def,
                name,
                kind,
                breaked: false,
            })
        })
        .to_label_id()
    }

    /// Make a `Node::BindingDef`.
    #[must_use]
    pub fn mk_binding(&mut self, binddef: BindingDef) -> BindingId {
        self.mk_node(hir::Node::BindingDef(binddef)).to_binding_id()
    }

    /// Make a `Node::ExternHeader`.
    #[must_use]
    pub fn mk_extern_header(
        &mut self,
        abi: Abi,
        span: Span,
        block_span: Option<Span>,
    ) -> ExternHeaderId {
        self.mk_node(hir::Node::ExternHeader(hir::ExternHeader {
            abi,
            span,
            block_span,
        }))
        .to_extern_header_id()
    }

    /// Make a gen trace.
    ///
    /// *NB: GenId is not a node.*
    pub fn mk_gen(&mut self, trace: GenTrace) -> GenId {
        self.pkg.traces.create(trace)
    }
}

/// Node generation methods `gen_`, make nodes to use when desugaring the ast
/// into hir, the nodes will also be marked as generated.
impl LoweringCtx {
    /// Marks a node as generated, should be called on every node generated: at
    /// least one per `gen_` method.
    pub fn mark_gen(&mut self, node_id: impl Into<NodeId>, genid: GenId) {
        self.pkg
            .generated
            .insert(self.hir_id(node_id.into()), genid);
    }

    /// Generate a `ExprKind::Block`.
    #[must_use]
    pub fn gen_block_expr(
        &mut self,
        label: Opt<LabelId>,
        stmts: Vec<hir::StmtId>,
        tail: Opt<ExprId>,
        span: Span,
        genid: GenId,
    ) -> ExprId {
        let block = self.mk_block(stmts, tail, span);

        let e = self.mk_expr(hir::ExprKind::Block(label, block), span);

        self.mark_gen(e, genid);

        e
    }

    /// Generate a `ExprKind::If`.
    #[must_use]
    pub fn gen_if_expr(
        &mut self,
        cond: ExprId,
        then: ExprId,
        els: Opt<ExprId>,
        span: Span,
        genid: GenId,
    ) -> ExprId {
        let e = self.mk_expr(hir::ExprKind::If(cond, then, els), span);

        self.mark_gen(e, genid);

        e
    }

    /// Generate a `ExprKind::Unary`.
    #[must_use]
    pub fn gen_unary_expr(&mut self, unop: UnOp, op: ExprId, span: Span, genid: GenId) -> ExprId {
        let e = self.mk_expr(hir::ExprKind::Unary(unop, op), span);

        self.mark_gen(e, genid);

        e
    }

    /// Generate a `ExprKind::Break`.
    #[must_use]
    pub fn gen_break_expr(
        &mut self,
        label: LabelId,
        expr: Opt<ExprId>,
        span: Span,
        genid: GenId,
    ) -> ExprId {
        let e = self.mk_expr(hir::ExprKind::Break(label, expr), span);

        self.mark_gen(e, genid);

        e
    }

    /// Generate a `StmtKind::Expr`.
    #[must_use]
    pub fn gen_expr_stmt(&mut self, expr: ExprId, span: Span, genid: GenId) -> StmtId {
        let s = self.mk_stmt(hir::StmtKind::Expr(expr), span);

        self.mark_gen(s, genid);

        s
    }
}

/// Lowering Methods
impl LoweringCtx {
    /// Lower an item
    pub fn lower_item(&mut self, item: &ast::Item) -> ReResult<ItemId> {
        self.reset_item_specific();

        match item {
            ast::Item::Fundef(fundef) => Ok(self.lower_fundef(fundef)),
            ast::Item::Fundecl(fundecl) => Ok(self.lower_fundecl(fundecl)),
            ast::Item::Globdef(globdef) => self.lower_globdef(globdef),
            ast::Item::Globdecl(globdecl) => Ok(self.lower_globdecl(globdecl)),
            ast::Item::Extern(extrn) => Ok(self.lower_extern(extrn)),
            ast::Item::Directive(directive) => self.lower_directive(directive),
        }
    }

    /// Lower a function definition.
    pub fn lower_fundef(&mut self, fundef: &ast::Fundef) -> ItemId {
        let sig = self.lower_sig(&fundef.sig);
        let body = self.lower_block(&fundef.block);

        self.mk_item(
            hir::ItemKind::Fundef(hir::Fundef {
                abi: fundef
                    .ext_header
                    .as_ref()
                    .map(|h| h.abi)
                    .unwrap_or_default(),
                name: fundef.name,
                sig,
                body,
            }),
            fundef.span,
        )
    }

    /// Lower a function signature
    pub fn lower_sig(&mut self, sig: &ast::Sig) -> hir::Sig {
        let ast::Sig {
            ref params,
            ref ret,
            span,
        } = *sig;

        let mut hir_params = Vec::with_capacity(params.len());

        for param in params {
            let ty = self.lower_type(&param.ty);
            hir_params.push(self.mk_param(param.name, ty, param.span));
        }

        let hir_ret = self.lower_otype(ret.as_ref());

        hir::Sig {
            params: hir_params,
            ret: hir_ret,
            span,
        }
    }

    /// Lower a type
    pub fn lower_type(&mut self, ty: &ast::Type) -> hir::TyId {
        let kind = match ty.kind {
            ast::TypeKind::Path(ref path) => hir::TypeKind::Path(self.lower_path(path)),
            ast::TypeKind::Pointer(mutability, ref pointee) => {
                let pointee = self.lower_type(pointee);

                hir::TypeKind::Pointer(mutability, pointee)
            }
            ast::TypeKind::Funptr(ref params, ref ret) => {
                let mut params_t = Vec::with_capacity(params.len());

                for param in params {
                    params_t.push(self.lower_type(param));
                }

                let ret = Opt::from(ret.as_ref().map(|ret| self.lower_type(ret)));

                hir::TypeKind::Funptr(params_t, ret)
            }
        };

        self.mk_type(kind, ty.span)
    }

    /// Lower a block
    pub fn lower_block(&mut self, block: &ast::Block) -> BlockId {
        let mut stmts = Vec::with_capacity(block.stmts.len());

        for stmt in &block.stmts {
            if let Ok(ostmt) = self.lower_stmt(stmt)
                && let Some(stmt) = ostmt.expand()
            {
                stmts.push(stmt);
            }
        }

        let tail = self.lower_oexpr(block.tail.as_ref());

        self.mk_block(stmts, tail, block.span)
    }

    /// Lower a statement
    pub fn lower_stmt(&mut self, stmt: &ast::Stmt) -> ReResult<Opt<StmtId>> {
        if stmt.kind == ast::StmtKind::Empty {
            return Ok(Opt::None);
        }

        let stmt_id = self.reserve_stmt(stmt.span);

        let kind = match stmt.kind {
            ast::StmtKind::BindingDef(mutability, name, ref ty, ref expr) => {
                let ty = self.lower_otype(ty.as_ref());
                let expr = self.lower_oexpr(expr.as_ref());

                let [_, binding_id] = self.mk_node_many(|[local_id, binding_id]| {
                    let local = hir::Node::Local(hir::Local {
                        name,
                        kind: LocalKind::UserBinding,
                        def: binding_id,
                    });

                    let binding = hir::Node::BindingDef(hir::BindingDef(
                        mutability,
                        name,
                        ty,
                        expr,
                        local_id.to_local_id(),
                        stmt.span,
                    ));

                    [local, binding]
                });

                hir::StmtKind::BindingDef(binding_id.to_binding_id())
            }
            ast::StmtKind::Directive(ref directive) => {
                hir::StmtKind::Directive(tri!(self.lower_directive(directive)))
            }
            ast::StmtKind::Expr(ref expr) => hir::StmtKind::Expr(tri!(self.lower_expr(expr))),
            ast::StmtKind::Semi(ref expr) => hir::StmtKind::Semi(tri!(self.lower_expr(expr))),
            ast::StmtKind::Empty => unreachable!(),
        };

        self.pop_stmt(stmt_id, kind);

        Ok(Opt::Some(stmt_id))
    }

    /// Lower an expression
    pub fn lower_expr(&mut self, expr: &ast::Expr) -> ReResult<ExprId> {
        // marks the current expression as generated if true.
        let mut generated: Opt<GenId> = Opt::None;

        // reserve a node for this expression.
        let expr_id = self.reserve_expr(expr.span);

        let kind = match &expr.kind {
            ast::ExprKind::Bool(bool) => hir::ExprKind::Bool(*bool),
            ast::ExprKind::Lit(lit) => hir::ExprKind::Lit(lit.clone()),
            ast::ExprKind::Paren(expr) => {
                self.free_reserved(expr_id);

                return self.lower_expr(expr);
            }
            ast::ExprKind::Path(path) => hir::ExprKind::Path(self.lower_path(path)),
            ast::ExprKind::Binary(lhs, binop, rhs) => hir::ExprKind::Binary(
                tri!(self.lower_expr(lhs)),
                *binop,
                tri!(self.lower_expr(rhs)),
            ),
            ast::ExprKind::Unary(unop, op) => {
                hir::ExprKind::Unary(*unop, tri!(self.lower_expr(op)))
            }
            ast::ExprKind::Borrow(mutability, op) => {
                hir::ExprKind::Borrow(*mutability, tri!(self.lower_expr(op)))
            }
            ast::ExprKind::Call(callee, args) => {
                let mut lowered_args = Vec::with_capacity(args.len());

                for arg in args {
                    lowered_args.push(tri!(self.lower_expr(arg)));
                }

                hir::ExprKind::Call(tri!(self.lower_expr(callee)), lowered_args)
            }
            ast::ExprKind::If(_, cond, then, els) => hir::ExprKind::If(
                tri!(self.lower_expr(cond)),
                tri!(self.lower_expr(then)),
                self.lower_oexpr(els.as_deref()),
            ),
            ast::ExprKind::Block(labeldef, block) => hir::ExprKind::Block(
                labeldef
                    .0
                    .map(|labeldef| {
                        self.lower_label_def(
                            &ast::LabelDef(Some(labeldef)),
                            hir::LabelKind::Block,
                            expr_id,
                        )
                    })
                    .into(),
                self.lower_block(block),
            ),
            // NB: here we desugar the while loop, we turn:
            //
            // ```lun
            // label: while condition {
            //     // body
            // }
            // ```
            //
            // into the following:
            //
            // ```lun
            // label: loop { // <- "the outer" block
            //     if !condition { // <- without the block here
            //         break :label;
            //     } else {
            //         // body
            //     };
            // }
            // ```
            ast::ExprKind::While(labeldef, cond, block) => {
                // lower the label
                let label =
                    Opt::Some(self.lower_label_def(labeldef, hir::LabelKind::While, expr_id));

                // lower the condition of the while expression
                let cond = tri!(self.lower_expr(cond));

                // make the generation trace
                let genid = self.mk_gen(GenTrace::While);

                // create the break expression of the then of the if.
                let brek = self.gen_break_expr(label.unwrap(), Opt::None, expr.span, genid); // NB: the unwrap is guaranteed to succeed.

                // lower the body loop
                let body = self.lower_block(block);
                let body_e = self.mk_expr(hir::ExprKind::Block(Opt::None, body), block.span);

                // create the if expression and its own condition
                let not_cond = self.gen_unary_expr(UnOp::Not, cond, expr.span, genid);
                let if_expr = self.gen_if_expr(not_cond, brek, Opt::Some(body_e), expr.span, genid);
                let if_stmt = self.gen_expr_stmt(if_expr, expr.span, genid);

                // create the "outer" block
                let block = self.mk_block(vec![if_stmt], Opt::None, block.span);

                generated = Opt::Some(genid);

                hir::ExprKind::Loop(label.unwrap(), block)
            }
            ast::ExprKind::For(..) => {
                self.dcx.emit(FeatureNotImplemented::new(
                    "for loops",
                    "for now use a while loop or an infinite loop",
                    expr.span,
                ));

                hir::ExprKind::Lit(Lit::int(0xDEAD_BEEF))
            }
            ast::ExprKind::Loop(labeldef, block) => {
                let label =
                    Opt::Some(self.lower_label_def(labeldef, hir::LabelKind::Loop, expr_id));

                hir::ExprKind::Loop(label.unwrap(), self.lower_block(block))
            }
            ast::ExprKind::Return(expr) => hir::ExprKind::Return(self.lower_oexpr(expr.as_deref())),
            ast::ExprKind::Break(label, op) => {
                let (label_id, def, kind) = if let Some(Spanned {
                    node: label_name,
                    span,
                }) = label.0
                {
                    let Some(hir::Label { id, def, kind, .. }) =
                        self.label_by_name(label_name.name).copied()
                    else {
                        return self
                            .dcx
                            .emit(UseOfUndefinedLabel {
                                name: label_name.name,
                                primary: span,
                            })
                            .cant_rec();
                    };

                    (id, def, kind)
                } else {
                    let Some(id) = self.label_stack.last().copied() else {
                        return self
                            .dcx
                            .emit(LabelKwOutsideLoopOrBlock {
                                kw: sym::Break,
                                primary: expr.span,
                            })
                            .cant_rec();
                    };

                    let hir::Label { kind, def, .. } = *self.get_label(id, false);

                    (id, def, kind)
                };

                let expr = if let Some(op) = op {
                    let expr_span = op.span;
                    let expr_id = tri!(self.lower_expr(op));

                    if !kind.can_have_expr() {
                        let def_span = self.get_node(def.0).span();

                        return self
                            .dcx
                            .emit(BreakWithValueUnsupported {
                                wher: kind.to_sym(),
                                expr_span,
                                break_span: expr.span,
                                def_span,
                            })
                            .cant_rec();
                    }

                    Opt::Some(expr_id)
                } else {
                    Opt::None
                };

                self.label_breaked(label_id);

                hir::ExprKind::Break(label_id, expr)
            }
            ast::ExprKind::Continue(label) => {
                let (label_id, def, kind) = if let Some(Spanned {
                    node: label_name,
                    span,
                }) = label.0
                {
                    let Some(hir::Label { id, def, kind, .. }) =
                        self.label_by_name(label_name.name).copied()
                    else {
                        return self
                            .dcx
                            .emit(UseOfUndefinedLabel {
                                name: label_name.name,
                                primary: span,
                            })
                            .cant_rec();
                    };

                    (id, def, kind)
                } else {
                    let Some(id) = self.label_stack.last().copied() else {
                        return self
                            .dcx
                            .emit(LabelKwOutsideLoopOrBlock {
                                kw: sym::Break,
                                primary: expr.span,
                            })
                            .cant_rec();
                    };

                    let hir::Label { kind, def, .. } = *self.get_label(id, false);

                    (id, def, kind)
                };

                if kind.is_block() {
                    let block_span = self.get_node(def.0).span();

                    self.dcx.emit(CantContinueABlock {
                        primary: expr.span,
                        block_span,
                    });
                }

                hir::ExprKind::Continue(label_id)
            }
            ast::ExprKind::Field(operand, member) => {
                let op = tri!(self.lower_expr(operand));

                hir::ExprKind::Field(op, *member)
            }
            ast::ExprKind::Cast(expr, ty) => {
                let expr = tri!(self.lower_expr(expr));
                let ty = self.lower_type(ty);

                hir::ExprKind::Cast(expr, ty)
            }
        };

        self.pop_expr(expr_id, kind);

        if let Some(genid) = generated.expand() {
            self.mark_gen(expr_id, genid);
        }

        Ok(expr_id)
    }

    /// Set the `breaked` of the label to true.
    pub fn label_breaked(&mut self, id: LabelId) {
        self.mut_label(id, false).breaked = true;
    }

    /// Bind a new label, and add it top of the label stack.
    pub fn bind_label(
        &mut self,
        name: Option<Spanned<Identifier>>,
        kind: hir::LabelKind,
        def: ExprId,
    ) -> LabelId {
        if let Some(name) = name
            && let Some(hir::Label {
                name: Some(Spanned { node: _, span }),
                ..
            }) = self.label_by_name(name.node.name)
        {
            self.dcx.emit(WLabelShadowed {
                name: name.node.name,
                first_decl: *span,
                primary: name.span,
            });
        }

        let label_id = self.mk_label(name, kind, def);

        self.label_stack.push(label_id);

        label_id
    }

    /// Tries to get a reference to the label with the name `needle` in the current
    /// label stack.
    pub fn label_by_name(&self, needle: Symbol) -> Option<&hir::Label> {
        for label_id in self.label_stack.iter().rev().copied() {
            let label = self.get_label(label_id, true);

            if let Some(name) = label.name
                && name.node.name == needle
            {
                return Some(label);
            }
        }

        None
    }

    /// Lower a label definition
    pub fn lower_label_def(
        &mut self,
        label: &ast::LabelDef,
        kind: hir::LabelKind,
        def: ExprId,
    ) -> LabelId {
        self.bind_label(label.0, kind, def)
    }

    /// Lower an optional type
    pub fn lower_otype(&mut self, ty: Option<&ast::Type>) -> Opt<TyId> {
        Opt::from(ty.map(|ty| self.lower_type(ty)))
    }

    /// Lower an optional expr
    pub fn lower_oexpr(&mut self, expr: Option<&ast::Expr>) -> Opt<ExprId> {
        if let Some(expr) = expr
            && let Ok(exprid) = self.lower_expr(expr).dere()
        {
            Opt::Some(exprid)
        } else {
            Opt::None
        }
    }

    /// Lower a function declaration.
    pub fn lower_fundecl(&mut self, fundecl: &ast::Fundecl) -> ItemId {
        let sig = self.lower_sig(&fundecl.sig);

        self.mk_item(
            hir::ItemKind::Fundecl(hir::Fundecl {
                ext: self.cur_ext,
                name: fundecl.name,
                sig,
            }),
            fundecl.span,
        )
    }

    /// Lower a global definition.
    pub fn lower_globdef(&mut self, globdef: &ast::Globdef) -> ReResult<ItemId> {
        let ty = self.lower_otype(globdef.ty.as_ref());
        let expr = tri!(self.lower_expr(&globdef.expr));

        Ok(self.mk_item(
            hir::ItemKind::Globdef(hir::Globdef {
                mutability: globdef.mutability,
                name: globdef.name,
                ty,
                expr,
            }),
            globdef.span,
        ))
    }

    /// Lower a global declaration.
    pub fn lower_globdecl(&mut self, globdecl: &ast::Globdecl) -> ItemId {
        let ty = self.lower_type(&globdecl.ty);

        self.mk_item(
            hir::ItemKind::Globdecl(hir::Globdecl {
                ext: self.cur_ext,
                mutability: globdecl.mutability,
                name: globdecl.name,
                ty,
            }),
            globdecl.span,
        )
    }

    /// Lower an extern block.
    pub fn lower_extern(&mut self, extrn: &ast::Extern) -> ItemId {
        let ext = self.mk_extern_header(extrn.header.abi, extrn.header.span, Some(extrn.span));

        let cur = self.cur_ext;
        if let Some(cur) = cur.expand() {
            let hir::Node::ExternHeader(hir::ExternHeader {
                block_span: Some(outer_span),
                ..
            }) = *self.get_node(cur.0)
            else {
                unreachable!();
            };

            self.dcx.emit(CannotNestExternBlocks {
                inner_span: extrn.span,
                outer_span,
            });
        }

        self.cur_ext = Opt::Some(ext);

        self.lower_item_seq(&extrn.items, self.cursor);

        self.cur_ext = cur;

        // NOTE: this is fine, we discard the result in every cases.
        ItemId(DefId::RESERVED)
    }

    /// Lower of a directive
    pub fn lower_directive(&mut self, directive: &ast::Directive) -> ReResult<ItemId> {
        match directive {
            ast::Directive::ModDef(moddef) => Ok(self.lower_moddef(moddef)),
            ast::Directive::ModDecl(moddecl) => self.lower_moddecl(moddecl),
            ast::Directive::Import(import) => Ok(self.lower_import(import)),
        }
    }

    /// Lower a module definition.
    pub fn lower_moddef(&mut self, moddef: &ast::ModDef) -> ItemId {
        let item_id = self.mk_item(
            hir::ItemKind::Directive(hir::Directive::Mod(
                moddef.name,
                hir::Mod::new(moddef.module.span),
            )),
            moddef.span,
        );

        self.lower_item_seq(&moddef.module.items, OwnerId(item_id.0));

        item_id
    }

    /// Lower a module declaration.
    pub fn lower_moddecl(&mut self, moddecl: &ast::ModDecl) -> ReResult<ItemId> {
        let sm = self.session.sm.clone();
        let parent_def = self.get_hirid(HirId::mk_owner(self.cursor));
        let parent_path = sm.ref_path(parent_def.span().fid);

        let name = moddecl.name.as_str();

        // 1. compute the path of the module
        let possible_paths: [PathBuf; _] = if self.cursor.is_package_root() {
            let mut nested = parent_path.with_file_name("");
            nested.push(name);
            nested.push("mod.mu");

            [
                // same dir
                parent_path.with_file_name(format!("{name}.mu")),
                // nested with mod.mu
                nested,
            ]
        } else {
            // same dir
            let mut same_dir = parent_path.with_extension("");
            same_dir.push(format!("{name}.mu"));

            // nested with mod.mu
            let mut nested = PathBuf::from(parent_path);
            nested.push(name);
            nested.push("mod.mu");

            [same_dir, nested]
        };

        let mod_path = match (
            sm.file_loader().file_exists(&possible_paths[0]),
            sm.file_loader().file_exists(&possible_paths[1]),
        ) {
            (true, true) => {
                return self
                    .dcx
                    .emit(ModuleFilePathErr::BothFiles {
                        name: moddecl.name.name,
                        paths: possible_paths,
                        primary: moddecl.span,
                    })
                    .cant_rec();
            }
            (false, false) => {
                return self
                    .dcx
                    .emit(ModuleFilePathErr::NoFiles {
                        name: moddecl.name.name,
                        paths: possible_paths,
                        primary: moddecl.span,
                    })
                    .cant_rec();
            }
            (true, false) => &possible_paths[0],
            (false, true) => &possible_paths[1],
        };

        // 2. add the file to the source map and retrieve its source code
        let mod_fid = sm.register(mod_path);
        let source = sm.ref_src(mod_fid);

        // 3. lex the module
        let mut lexer = Lexer::new(source, self.session.clone(), mod_fid);
        let tokenstream = lexer.produce().dere_or(TokenStream::new_sealed);

        // 4. parse the module
        self.parser.clear(tokenstream);
        let mod_ast = self.parser.produce().dere_or(|| ast::Mod {
            items: Vec::new(),
            span: sm.file_span(mod_fid),
        });

        // 5. lower to HIR.
        let item_id = self.mk_item(
            hir::ItemKind::Directive(hir::Directive::Mod(
                moddecl.name,
                hir::Mod::new(mod_ast.span),
            )),
            moddecl.span,
        );

        self.lower_item_seq(&mod_ast.items, OwnerId(item_id.0));

        Ok(item_id)
    }

    /// Lower an AST Path to an HIR Path
    pub fn lower_path(&mut self, path: &ast::Path) -> PathId {
        let mut segments = Vec::new();

        for seg in &path.segments {
            match seg {
                ast::PathSegment::Ident(ident) => {
                    let res = self.mk_res(hir::Res::Unresolved);
                    segments.push(self.mk_path_segment(*ident, res))
                }
                ast::PathSegment::Pkg(span) => {
                    let res = self.mk_res(hir::Res::Def(hir::DefKind::Mod, DefId::PACKAGE_DEF));

                    segments.push(self.mk_path_segment(Identifier::new(sym::Pkg, *span), res))
                }
            }
        }

        // NB: we are ensured there is at least one segment in the path so it will never panic.
        let lo = path.segments.first().map(|seg| seg.span()).unwrap();
        let hi = path.segments.last().map(|seg| seg.span()).unwrap();

        let res = self.mk_res(hir::Res::Unresolved);

        self.mk_path(hir::Path::new(res, segments, Span::join(lo, hi)))
    }

    /// Lower an import directive
    pub fn lower_import(&mut self, import: &ast::Import) -> ItemId {
        let path = self.lower_path(&import.path);

        self.mk_item(
            hir::ItemKind::Directive(hir::Directive::Import {
                path,
                alias: import.alias,
            }),
            import.span,
        )
    }

    /// Lower a sequence of items in *owner*.
    pub fn lower_item_seq(&mut self, items: &[ast::Item], owner: OwnerId) {
        let prev = self.cursor;
        self.cursor = owner;

        for item in items {
            // NB: we discard the result but it's fine because the diagnostic
            // was already emitted (in case of error) and we don't care about
            // the item id.
            _ = self.lower_item(item);
        }

        self.cursor = prev;
    }
}
