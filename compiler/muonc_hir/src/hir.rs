//! HIR data types.

use std::fmt;

use indexmap::IndexMap;
use muonc_entity::{Entity, EntityMap, Opt, entity};
use muonc_middle::ast::{Abi, BinOp, Mutability, PrimTy, UnOp, Visibility};
use muonc_span::prelude::*;
use muonc_token::Lit;

/// Kind of definition in Muon
#[derive(Debug, Clone, Copy)]
pub enum DefKind {
    /// Module kind of definiton
    ///
    /// `#mod ...`
    Mod,
    /// Function definition/declaration
    ///
    /// `foo :: fun() {}` or
    /// `foo :: fun();`
    Fun,
    /// Glob definition/declaration
    ///
    /// `mut bar = 12;` or
    /// `bar: u32;`
    Glob,
    /// Import directive
    ///
    /// `#import ...;`
    Import,
    /// Extern block
    ///
    /// `extern "C" { /* ... */ }`
    Extern,
}

impl DefKind {
    /// Returns true if this kind can have a child
    pub fn can_child(&self) -> bool {
        matches!(self, DefKind::Mod)
    }
}

impl fmt::Display for DefKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Mod => write!(f, "Mod"),
            Self::Fun => write!(f, "Fun"),
            Self::Glob => write!(f, "Glob"),
            Self::Import => write!(f, "Import"),
            Self::Extern => write!(f, "Extern"),
        }
    }
}

/// The resolution of a path or export.
#[derive(Debug, Clone)]
pub enum Res {
    /// Resolved to a definition of some sort in the HIR.
    ///
    /// **Do not belong to a specific namespace**
    Def(DefKind, DefId),
    /// A primitive type
    ///
    /// **Belongs to the type namespace**
    PrimTy(PrimTy),
    /// A local variable or function parameter.
    ///
    /// **Belongs to the value namespace**
    Local(HirId<LocalId>),
    /// Marks an unresolved path.
    ///
    /// *NB: this is unreachable after name resolution.*
    Unresolved,
}

impl Res {
    /// Returns `Some(self)` if self isn't `Res::Unresolved`.
    #[must_use]
    pub fn ensure_res(self) -> Option<Self> {
        match self {
            Res::Unresolved => None,
            _ => Some(self),
        }
    }

    /// Returns `true` if the res is [`Unresolved`].
    ///
    /// [`Unresolved`]: Res::Unresolved
    #[must_use]
    pub fn is_unresolved(&self) -> bool {
        matches!(self, Self::Unresolved)
    }

    /// Get a displayable symbol representing this name resolution
    pub fn to_symbol(&self) -> Symbol {
        match self {
            Res::Def(kind, _) => match kind {
                DefKind::Mod => sym::module,
                DefKind::Fun => sym::function,
                DefKind::Glob => sym::global,
                DefKind::Import => sym::import,
                DefKind::Extern => sym::extern_res,
            },
            Res::PrimTy(_) => sym::primty,
            Res::Local(_) => sym::local,
            Res::Unresolved => unreachable!(),
        }
    }
}

impl From<PrimTy> for Res {
    fn from(v: PrimTy) -> Self {
        Self::PrimTy(v)
    }
}

/// A resolved Path
#[derive(Debug, Clone)]
pub struct Path {
    pub res: Res,
    pub segments: Vec<PathSegmentId>,
    pub span: Span,
}

impl Path {
    /// Create a new unresolved path.
    pub fn new(segments: Vec<PathSegmentId>, span: Span) -> Path {
        Path {
            res: Res::Unresolved,
            segments,
            span,
        }
    }
}

/// A segment of a resolved path.
#[derive(Debug, Clone)]
pub struct PathSegment {
    pub ident: Identifier,
    pub id: PathSegmentId,
    pub res: Res,
}

impl TryFrom<Node> for PathSegment {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::PathSegment(seg) = node {
            Ok(seg)
        } else {
            Err(())
        }
    }
}

entity! {
    /// Uniquely identifies `Node`s but local to an [`OwnerId`].
    pub struct NodeId {
        const ZERO = 0;
    }

    /// [`NodeId`] but ensured by its type to point to a `Node::Block`.
    pub struct BlockId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Type`.
    pub struct TypId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Param`.
    pub struct ParamId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Expr`.
    pub struct ExprId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Stmt`.
    pub struct StmtId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Label`.
    pub struct LabelId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::PathSegment`.
    pub struct PathSegmentId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Binding`.
    pub struct BindingId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Local`.
    pub struct LocalId = NodeId;

    /// [`NodeId`] but ensured by its type to point to a `Node::Path`.
    pub struct PathId = NodeId;

    /// [`DefId`] but ensured that the Item that points to can *own* items, like
    /// Muon's modules or extern blocks.
    ///
    /// NB: the item that "represents" the owner (like `Item::Extern` or
    /// `Item::Mod`) always has the `NodeId::ZERO`.
    pub struct OwnerId = DefId;

    /// Just an alias to make it obvious that it points to an HIR Item in the
    /// current package being built.
    pub struct ItemId = DefId;

    /// Id of a generation trace.
    pub struct GenId {}
}

impl NodeId {
    /// Convert this node id to a block id.
    pub fn to_block_id(self) -> BlockId {
        BlockId(self)
    }

    /// Convert this node id to a type id.
    pub fn to_typ_id(self) -> TypId {
        TypId(self)
    }

    /// Convert this node id to a param id.
    pub fn to_param_id(self) -> ParamId {
        ParamId(self)
    }

    /// Convert this node id to a expr id.
    pub fn to_expr_id(self) -> ExprId {
        ExprId(self)
    }

    /// Convert this node id to a stmt id.
    pub fn to_stmt_id(self) -> StmtId {
        StmtId(self)
    }

    /// Convert this node id to a label id.
    pub fn to_label_id(self) -> LabelId {
        LabelId(self)
    }

    /// Convert this node id to a path segment id.
    pub fn to_path_segment_id(self) -> PathSegmentId {
        PathSegmentId(self)
    }

    /// Convert this node id to a binding id.
    pub fn to_binding_id(self) -> BindingId {
        BindingId(self)
    }

    /// Convert this node id to a local id.
    pub fn to_local_id(self) -> LocalId {
        LocalId(self)
    }

    /// Convert this node id to a Path id.
    pub fn to_path_id(self) -> PathId {
        PathId(self)
    }
}

impl fmt::Display for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node{}", self.index())
    }
}

/// Denotes an id type that points to a node with a specific type.
pub trait NodeType: Into<NodeId> {
    type NodeTy;

    /// Turns `&Node` into `&Self::NodeTy`
    fn convert(node: &Node) -> Option<&Self::NodeTy>;

    /// Turns `&mut Node` into `&mut Self::NodeTy`
    fn convert_mut(node: &mut Node) -> Option<&mut Self::NodeTy>;
}

impl NodeType for NodeId {
    type NodeTy = Node;

    fn convert(node: &Node) -> Option<&Node> {
        Some(node)
    }

    fn convert_mut(node: &mut Node) -> Option<&mut Node> {
        Some(node)
    }
}

macro_rules! node_type_impl {
    () => {};
    ($id:ident => $node_t:ident $(, $($rest:tt)*)?) => {
        impl From<$id> for NodeId {
            fn from(id: $id) -> Self {
                id.0
            }
        }

        impl NodeType for $id {
            type NodeTy = $node_t;

            fn convert(node: &Node) -> Option<&Self::NodeTy> {
                if let Node::$node_t(n) = node {
                    Some(n)
                } else {
                    None
                }
            }

            fn convert_mut(node: &mut Node) -> Option<&mut Self::NodeTy> {
                if let Node::$node_t(n) = node {
                    Some(n)
                } else {
                    None
                }
            }
        }

        $(
            node_type_impl!($($rest)*);
        )?
    };
}

node_type_impl!(
    BlockId => Block,
    TypId => Type,
    ParamId => Param,
    ExprId => Expr,
    StmtId => Stmt,
    LabelId => Label,
    PathSegmentId => PathSegment,
    BindingId => BindingDef,
    LocalId => Local,
    PathId => Path,
);

impl OwnerId {
    /// Is this owner the package root?
    pub fn is_package_root(&self) -> bool {
        self.0 == DefId::PACKAGE_DEF
    }
}

impl fmt::Display for OwnerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "o{}", self.index())
    }
}

/// Traces of desugaring
#[derive(Debug, Clone)]
pub enum GenTrace {
    While,
}

/// HIR id, uniquely identifies `Node`s in a whole `Package`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HirId<Id: NodeType = NodeId> {
    pub owner: OwnerId,
    pub node_id: Id,
}

impl<Id: fmt::Display + NodeType> fmt::Display for HirId<Id> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}@{}", self.node_id, self.owner)
    }
}

impl HirId {
    /// Make an HIR Id from the owner, always "points" to the item
    /// "representing" the owner, see [`OwnerId`] documentation for more
    /// informations.
    pub fn mk_owner(owner: OwnerId) -> HirId {
        HirId {
            owner,
            node_id: NodeId::ZERO,
        }
    }
}

/// Kind of reservation
#[derive(Debug, Clone, PartialEq)]
pub enum ReservationKind {
    Expr,
    Stmt,
}

/// A node of the HIR
#[derive(Debug, Clone)]
pub enum Node {
    Package(Mod),
    Item(Item),
    Param(Param),
    Type(Type),
    Block(Block),
    Stmt(Stmt),
    Expr(Expr),
    PathSegment(PathSegment),
    Label(Label),
    BindingDef(BindingDef),
    Local(Local),
    Path(Path),
    Reserved(ReservationKind, Span),
}

impl Node {
    /// Return an `Some(item)` if `self == Node::Item(item)`.
    pub fn as_item(&self) -> Option<&Item> {
        if let Self::Item(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Return an `Some(item)` if `self == Node::Item(item)`.
    pub fn as_item_mut(&mut self) -> Option<&mut Item> {
        if let Self::Item(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns the span of the node
    pub fn span(&self) -> Span {
        match self {
            Node::Package(Mod { span, .. })
            | Node::Item(Item { span, .. })
            | Node::Param(Param { span, .. })
            | Node::Type(Type { span, .. })
            | Node::Block(Block { span, .. })
            | Node::Stmt(Stmt { span, .. })
            | Node::Expr(Expr { span, .. })
            | Node::PathSegment(PathSegment {
                ident: Identifier { span, .. },
                ..
            })
            | Node::BindingDef(BindingDef(.., span))
            | Node::Local(Local {
                name: Identifier { span, .. },
                ..
            })
            | Node::Path(Path { span, .. })
            | Node::Reserved(_, span) => *span,
            Node::Label(Label { name, .. }) => {
                if let Some(name) = name {
                    name.span
                } else {
                    panic!("this label doesn't have a span")
                }
            }
        }
    }

    /// Returns `true` if the node is [`Reserved`].
    ///
    /// [`Reserved`]: Node::Reserved
    #[must_use]
    pub fn is_reserved(&self, kind: ReservationKind) -> bool {
        matches!(self, Self::Reserved(got, _) if *got == kind)
    }
}

/// The top-level data structure of HIR, stores the package being currently
/// compiled.
#[derive(Debug, Clone, Default)]
pub struct Package {
    /// the node owners
    pub owners: EntityMap<DefId, MaybeOwner>,
    /// a map of HirId that were generated when lowering, it will help to know
    /// what is generated or not and what it came from.
    pub generated: IndexMap<HirId, GenId>,
    /// the generated traces
    pub traces: EntityMap<GenId, GenTrace>,
}

impl Package {
    /// Create a new HIR Package.
    pub(super) fn new() -> Package {
        Package::default()
    }

    /// Get the node with the given HirId.
    pub fn get_node<Id: NodeType>(&self, hir_id: HirId<Id>) -> &Id::NodeTy {
        Id::convert(
            self.owners
                .get(hir_id.owner.0)
                .unwrap()
                .nodes
                .get(hir_id.node_id.into()),
        )
        .expect("HirId points to invalid node kind")
    }

    /// Mutable `get_node`.
    pub fn mut_node<Id: NodeType>(&mut self, hir_id: HirId<Id>) -> &mut Id::NodeTy {
        Id::convert_mut(
            self.owners
                .get_mut(hir_id.owner.0)
                .unwrap_mut()
                .nodes
                .get_mut(hir_id.node_id.into()),
        )
        .expect("HirId points to invalid node kind")
    }

    /// Get a reference to the given item.
    ///
    /// *NB: due to the borrow checker being dumb we cannot make the `get_item`
    /// method be `mut_item` and just return a mutable reference, it keeps
    /// complaining and i think it's not possible without unsafe rust.*
    pub fn get_item(&self, item: ItemId) -> &Item {
        match self.owners.get(item.0) {
            MaybeOwner::Owner(owner) => owner.nodes.get(NodeId::ZERO),
            MaybeOwner::NonOwner(hir_id) => self.get_node(*hir_id),
        }
        .as_item()
        .expect("an item")
    }

    /// Get a mutable reference to a maybe owner of nodes.
    pub fn get_maybe(&self, item: ItemId) -> &MaybeOwner {
        self.owners.get(item.0)
    }

    /// Mutable `get_maybe`.
    pub fn mut_maybe(&mut self, item: ItemId) -> &mut MaybeOwner {
        self.owners.get_mut(item.0)
    }
}

#[derive(Debug, Clone)]
pub enum MaybeOwner {
    /// An [`Item`] that **can** own [`Node`]s, like `Item::Mod` or
    /// `Item::Extern`.
    Owner(NodeOwner),
    /// An [`Item`] that can't own [`Node`]s
    NonOwner(HirId),
}

impl MaybeOwner {
    /// Convert maybe owner to an optional node owner.
    pub fn as_owner(&self) -> Option<&NodeOwner> {
        if let Self::Owner(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Unwrap the node owner, panics if it's not a node owner.
    #[track_caller]
    pub fn unwrap(&self) -> &NodeOwner {
        self.as_owner()
            .unwrap_or_else(|| panic!("Not an HIR owner"))
    }

    /// Mutable `MaybeOwner::as_owner`.
    pub fn as_owner_mut(&mut self) -> Option<&mut NodeOwner> {
        if let Self::Owner(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Mutable `MaybeOwner::unwrap`.
    #[track_caller]
    pub fn unwrap_mut(&mut self) -> &mut NodeOwner {
        self.as_owner_mut()
            .unwrap_or_else(|| panic!("Not an HIR owner"))
    }
}

/// A [`Node`] owner, see [`OwnerId`] for more details.
#[derive(Debug, Clone)]
pub struct NodeOwner {
    /// the owned HIR nodes
    pub nodes: EntityMap<NodeId, Node>,
}

impl NodeOwner {
    /// Get the list of owned item ids.
    pub fn items(&self) -> &[ItemId] {
        match self.nodes.get(NodeId::ZERO) {
            Node::Package(Mod { items, .. })
            | Node::Item(Item {
                kind:
                    ItemKind::Extern(Extern { items, .. })
                    | ItemKind::Directive(Directive::Mod(_, Mod { items, .. })),
                ..
            }) => items,
            _ => panic!("Node isn't an item owner"),
        }
    }

    /// Mutable `NodeOwner::items`.
    pub fn mut_items(&mut self) -> &mut Vec<ItemId> {
        match self.nodes.get_mut(NodeId::ZERO) {
            Node::Package(Mod { items, .. })
            | Node::Item(Item {
                kind:
                    ItemKind::Extern(Extern { items, .. })
                    | ItemKind::Directive(Directive::Mod(_, Mod { items, .. })),
                ..
            }) => items,
            _ => panic!("Node isn't an item owner"),
        }
    }

    /// Push an item id in the owner definition, see documentation of
    /// [`OwnerId`] for more information.
    ///
    /// *NB: this function panics if the item isn't an owner.*
    pub fn push_items(&mut self, item_id: ItemId) {
        self.mut_items().push(item_id)
    }
}

/// A Muon Module in HIR.
#[derive(Debug, Clone)]
pub struct Mod {
    /// visibility of module.
    pub vis: Visibility,
    /// the list of item ids this module owns.
    pub items: Vec<ItemId>,
    /// inner span of the module, see [`ast::Mod::span`].
    ///
    /// [`ast::Mod::span`]: muonc_parser::ast::Mod::span
    pub span: Span,
}

impl Mod {
    /// Create a new module.
    pub fn new(vis: Visibility, span: Span) -> Mod {
        Mod {
            vis,
            items: vec![],
            span,
        }
    }
}

/// A Muon Item in HIR
#[derive(Debug, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
}

impl Item {
    /// Get the name of the item.
    pub fn name(&self) -> Option<Symbol> {
        match &self.kind {
            ItemKind::Fundef(fundef) => Some(fundef.name.name),
            ItemKind::Fundecl(fundecl) => Some(fundecl.name.name),
            ItemKind::Globdef(globdef) => Some(globdef.name.name),
            ItemKind::Globdecl(globdecl) => Some(globdecl.name.name),
            ItemKind::Extern(_) => None,
            ItemKind::Directive(directive) => directive.name(),
        }
    }

    /// Get the defkind.
    pub fn defkind(&self) -> DefKind {
        match &self.kind {
            ItemKind::Fundef(_) | ItemKind::Fundecl(_) => DefKind::Fun,
            ItemKind::Globdef(_) | ItemKind::Globdecl(_) => DefKind::Glob,
            ItemKind::Directive(directive) => directive.defkind(),
            _ => todo!(),
        }
    }
}

/// A Muon Item kind in HIR
#[derive(Debug, Clone)]
pub enum ItemKind {
    /// Function definition item
    Fundef(Fundef),
    /// Function declaration item
    Fundecl(Fundecl),
    /// Global definition item
    Globdef(Globdef),
    /// Global declaration item
    Globdecl(Globdecl),
    /// Extern block item
    Extern(Extern),
    /// Directive.
    Directive(Directive),
}

impl ItemKind {
    /// Returns `true` if the item kind can own nodes.
    #[must_use]
    pub fn can_own(&self) -> bool {
        matches!(self, Self::Extern(..) | Self::Directive(Directive::Mod(..)))
    }
}

/// A Muon fundef in HIR
#[derive(Debug, Clone)]
pub struct Fundef {
    pub vis: Visibility,
    pub name: Identifier,
    pub sig: Sig,
    pub body: BlockId,
}

/// A Muon function signature
#[derive(Debug, Clone)]
pub struct Sig {
    pub params: Vec<ParamId>,
    pub ret: Opt<TypId>,
    pub span: Span,
}

impl Sig {
    /// Create a new empty function signature.
    pub fn new(span: Span) -> Sig {
        Sig {
            params: Vec::new(),
            ret: Opt::None,
            span,
        }
    }
}

/// A function parameter in HIR
#[derive(Debug, Clone)]
pub struct Param {
    pub name: Identifier,
    pub typ: TypId,
    pub span: Span,
    pub local: LocalId,
}

impl TryFrom<Node> for Param {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Param(param) = node {
            Ok(param)
        } else {
            Err(())
        }
    }
}

/// A Muon function declaration in HIR
#[derive(Debug, Clone)]
pub struct Fundecl {
    pub vis: Visibility,
    pub name: Identifier,
    pub sig: Sig,
}

/// A Muon global definition in HIR
#[derive(Debug, Clone)]
pub struct Globdef {
    pub vis: Visibility,
    pub mutability: Mutability,
    pub name: Identifier,
    pub typ: Opt<TypId>,
    pub expr: ExprId,
}

/// A Muon global declaration in HIR
#[derive(Debug, Clone)]
pub struct Globdecl {
    pub vis: Visibility,
    pub mutability: Mutability,
    pub name: Identifier,
    pub typ: TypId,
}

/// A Muon extern block in HIR
#[derive(Debug, Clone)]
pub struct Extern {
    pub abi: Abi,
    pub items: Vec<ItemId>,
}

/// Muon directive
#[derive(Debug, Clone)]
pub enum Directive {
    /// Module directive, its name and the modules.
    Mod(Identifier, Mod),
    /// Import directive
    Import {
        vis: Visibility,
        path: PathId,
        alias: Option<Identifier>,
    },
}

impl Directive {
    /// Get the name of the directive
    pub fn name(&self) -> Option<Symbol> {
        match self {
            Directive::Mod(ident, _) => Some(ident.name),
            Directive::Import { .. } => None,
        }
    }

    /// Get the defkind of the directive.
    pub fn defkind(&self) -> DefKind {
        match self {
            Directive::Mod(..) => DefKind::Mod,
            Directive::Import { .. } => DefKind::Import,
        }
    }
}

/// A Muon type in HIR
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

impl TryFrom<Node> for Type {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Type(ty) = node {
            Ok(ty)
        } else {
            Err(())
        }
    }
}

/// A Muon type kind in HIR.
#[derive(Debug, Clone)]
pub enum TypeKind {
    /// Path to a type
    Path(PathId),
    /// (Mutable) pointer.
    Pointer(Mutability, TypId),
    /// Function pointer.
    Funptr(Vec<TypId>, Opt<TypId>),
}

/// A Muon block in HIR
#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: Vec<StmtId>,
    pub tail: Opt<ExprId>,
    pub span: Span,
}

impl TryFrom<Node> for Block {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Block(blk) = node {
            Ok(blk)
        } else {
            Err(())
        }
    }
}

/// A Muon statement in HIR
#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

impl TryFrom<Node> for Stmt {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Stmt(stmt) = node {
            Ok(stmt)
        } else {
            Err(())
        }
    }
}

/// A user binding definition.
#[derive(Debug, Clone)]
pub struct BindingDef(
    pub Mutability,
    pub Identifier,
    pub Opt<TypId>,
    pub Opt<ExprId>,
    pub LocalId,
    pub Span,
);

/// Local kind
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Hash)]
pub enum LocalKind {
    /// a local introduced by a binding def statement.
    UserBinding,
    /// a local introduced by a parameter.
    Param,
}

/// A Local
#[derive(Debug, Clone)]
pub struct Local {
    /// name of the local, where it is defined.
    pub name: Identifier,
    /// kind of local
    pub kind: LocalKind,
    /// the node that defines the local.
    ///
    /// *NB: for now it's either a `Node::Param`, or a `Node::BindingDef`.*
    pub def: NodeId,
}

/// A Muon statement kind in HIR
#[derive(Debug, Clone)]
pub enum StmtKind {
    /// A local definition
    BindingDef(BindingId),
    /// A directive
    Directive(ItemId),
    /// An expression statement
    Expr(ExprId),
}

/// A Muon expression in HIR
#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

impl TryFrom<Node> for Expr {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Expr(expr) = node {
            Ok(expr)
        } else {
            Err(())
        }
    }
}

/// A Muon expression kind in HIR
#[derive(Debug, Clone)]
pub enum ExprKind {
    /// boolean expression (e.g: `true` / `false`)
    Bool(bool),
    /// literal expression (e.g: `12`, `6.7`, `"Hello World!"`)
    Lit(Lit),
    /// path expression (e.g: `core::panic`)
    Path(PathId),
    /// a binary expression (e.g: `1 + 2`, `x / 4`)
    Binary(ExprId, BinOp, ExprId),
    /// a unary expression (e.g: `-1`, `x.*`)
    Unary(UnOp, ExprId),
    /// a borrow expression (e.g: `&x`, `&mut x`)
    Borrow(Mutability, ExprId),
    /// a call expression (e.g: `println("Hello world!");`)
    Call(ExprId, Vec<ExprId>),
    /// an if expression (e.g: `if x { 1 } else { 2 }`, `if (x) 1 else 2`)
    If(ExprId, ExprId, Opt<ExprId>),
    /// a block expression (e.g: `{ /* ... */ }`, `a: { /* ... */ }`)
    ///
    /// *NB: a block may only have a label if it's named, because unlabeled
    /// block cannot be the target of a `break`.*
    Block(Opt<LabelId>, BlockId),
    /// a loop expression (e.g: `loop { /* ... */ }`, `a: loop { /* ... */ }`)
    Loop(LabelId, BlockId),
    /// a return expression (e.g: `return`, `return 12`)
    Return(Opt<ExprId>),
    /// a break expression (e.g: `break :a 12`, `break 12`, `break`)
    Break(LabelId, Opt<ExprId>),
    /// a continue expression (e.g: `continue :a 12`, `continue`)
    Continue(LabelId),
    /// a field expression (e.g: `x.a`)
    Field(ExprId, Identifier),
    /// a cast expression (e.g: `x as u32`)
    Cast(ExprId, TypId),
}

/// A kind of label.
#[derive(Debug, Clone, Copy)]
pub enum LabelKind {
    /// a label on a block.
    Block,
    /// a label on a loop.
    Loop,
    /// a label on a while.
    While,
}

impl LabelKind {
    /// Can this label kind supports having an expression on its break
    /// expression?
    #[must_use]
    pub fn can_have_expr(&self) -> bool {
        matches!(self, Self::Block | Self::Loop)
    }

    /// Returns `true` if the label kind is [`Block`].
    ///
    /// [`Block`]: LabelKind::Block
    #[must_use]
    pub fn is_block(&self) -> bool {
        matches!(self, Self::Block)
    }

    /// *Like to_string but the symbol edition.*
    #[must_use]
    pub fn to_sym(&self) -> Symbol {
        match self {
            Self::Block => Symbol::intern("block"),
            Self::Loop => sym::Loop,
            Self::While => sym::While,
        }
    }
}

/// A Muon label in HIR.
#[derive(Debug, Clone, Copy)]
pub struct Label {
    /// id of itself
    pub id: LabelId,
    /// the expression that defined this label
    pub def: ExprId,
    /// name of the label if any
    ///
    /// *NB: the span of the `Spanned` is the span of the entire label with the
    /// `:`.*
    pub name: Option<Spanned<Identifier>>,
    /// kind of label
    pub kind: LabelKind,
    /// did we `break` out of the definition of this label?
    pub breaked: bool,
}

impl Label {
    /// Set the definition to expr.
    pub fn set_def(&mut self, expr: ExprId) {
        debug_assert!(self.def.is_reserved());
        debug_assert!(!expr.is_reserved());

        self.def = expr;
    }
}

impl TryFrom<Node> for Label {
    type Error = ();

    fn try_from(node: Node) -> Result<Self, Self::Error> {
        if let Node::Label(label) = node {
            Ok(label)
        } else {
            Err(())
        }
    }
}

/// The scope of a definition.
#[derive(Debug, Clone)]
pub struct Scope {
    pub def: DefId,
    pub kind: DefKind,
}
