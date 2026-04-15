//! Name resolution of HIR, the next stage after lowering.

use either::Either;
use indexmap::IndexMap;
use muonc_utils::suggest_similar;
use std::{
    fmt::{self, Write},
    iter::zip,
    mem,
};

use crate::{
    diags::{AmbiguousName, NameDefinedMultipleTimes, NotFoundInScope},
    hir::*,
    visit::{DefContext, MutVisitor, NameContext, Namespace, PerNS, ScopeEvent},
};
use muonc_errors::prelude::*;
use muonc_middle::ast::PrimTy;
use muonc_span::{prelude::*, symbol::category_iter};

/// The name resolution utility
#[derive(Debug)]
pub struct Resolver<'hir> {
    pub(crate) pkg: &'hir mut Package,
    /// type symbol table
    pub(crate) type_st: SymbolTable,
    /// value symbol table
    pub(crate) value_st: SymbolTable,
    /// the current owner where we are resolving
    pub(crate) cur: OwnerId,
    /// the diagnostic context
    pub(crate) dcx: DiagCtxt,
}

impl<'hir> Resolver<'hir> {
    /// Create a new name resolver.
    pub fn new(pkg: &'hir mut Package, dcx: DiagCtxt) -> Resolver<'hir> {
        // create the type namespace
        let mut outer_ts = TableEntry::new();

        let mut mk_res = |res: Res| -> HirId<ResId> {
            HirId {
                owner: OwnerId(DefId::PACKAGE_DEF),
                node_id: pkg
                    .mut_maybe(ItemId(DefId::PACKAGE_DEF))
                    .unwrap_mut()
                    .nodes
                    .create(Node::Res(res))
                    .to_res_id(),
            }
        };

        for sym in category_iter(categories::PRIMITIVE_RANGE) {
            let res = mk_res(Res::PrimTy(
                PrimTy::from_symbol(sym).expect("the iterator is messed up"),
            ));

            outer_ts.entries.insert(sym, Entry::new(res));
        }

        let res = mk_res(Res::Def(DefKind::Mod, DefId::PACKAGE_DEF));
        outer_ts.entries.insert(sym::Pkg, Entry::new(res));

        let type_ns = SymbolTable::with_entry(outer_ts);

        // create the value namespace
        let val_ns = SymbolTable::new();

        Resolver {
            pkg,
            type_st: type_ns,
            value_st: val_ns,
            cur: OwnerId(DefId::PACKAGE_DEF),
            dcx,
        }
    }

    /// Resolve the HIR.
    pub fn resolve(&mut self) -> ReResult<()> {
        _ = self.type_st;
        _ = self.value_st;

        self.visit_package();

        if self.dcx.failed() {
            return Err(Recovered::Yes((), self.dcx.has_emitted().unwrap()));
        }

        Ok(())
    }

    /// Enter a new scope in both the type and value namespace.
    pub fn enter_scope(&mut self) {
        self.type_st.enter_scope();
        self.value_st.enter_scope();
    }

    /// Enter a new scope in both the type and value namespace.
    pub fn leave_scope(&mut self) {
        self.type_st.exit_scope();
        self.value_st.exit_scope();
    }

    /// Lookup in both namespaces.
    pub fn lookup(&mut self, name: Symbol) -> PerNS<Option<HirId<ResId>>> {
        PerNS {
            type_ns: self.type_st.lookup(name),
            value_ns: self.value_st.lookup(name),
        }
    }

    /// Bind `name` to `res` in the namespace `ns` at the current scope.
    pub fn bind(&mut self, name: Symbol, res: HirId<ResId>, ns: Namespace) {
        let symtable = match ns {
            Namespace::Type => &mut self.type_st,
            Namespace::Value => &mut self.value_st,
        };

        if let Some(old_res) = symtable.lookup(name)
            && !self.can_shadow(res, old_res)
            && self.pkg.ne_node(old_res, res)
        {
            self.dcx.emit(NameDefinedMultipleTimes {
                name,
                new_span: self
                    .res_span(Either::Left(res))
                    .expect("a definition always has a span"),
                old_span: self
                    .res_span(Either::Left(old_res))
                    .expect("a definition always has a span"),
            });
            return;
        }

        // reborrow because borrow checker is annoying
        let symtable = match ns {
            Namespace::Type => &mut self.type_st,
            Namespace::Value => &mut self.value_st,
        };

        symtable.inner_mut().entries.insert(name, Entry::new(res));
    }

    /// Returns `true` if `new` can shadow `old`.
    pub fn can_shadow(&self, new: HirId<ResId>, old: HirId<ResId>) -> bool {
        // NOTE: for now it's super simple shadowing rules but it may be broaden
        // later.

        let new = self.pkg.get_node(new);
        let old = self.pkg.get_node(old);

        match (new, old) {
            (Res::Local(new_id), Res::Local(old_id)) => {
                let new_local = self.pkg.get_node(*new_id);
                let old_local = self.pkg.get_node(*old_id);

                !(new_local.kind == LocalKind::Param && old_local.kind == LocalKind::Param)
            }
            _ => false,
        }
    }

    /// Get a node located in the current owner.
    pub fn get_node<Id: NodeType>(&self, id: Id) -> &Id::NodeTy {
        self.pkg.get_node(HirId {
            owner: self.cur,
            node_id: id,
        })
    }

    /// Mutable `get_node`.
    pub fn mut_node<Id: NodeType>(&mut self, id: Id) -> &mut Id::NodeTy {
        self.pkg.mut_node(HirId {
            owner: self.cur,
            node_id: id,
        })
    }

    /// Get the scope of the children.
    pub fn child_scope(&mut self, res: Either<HirId<ResId>, &Res>) -> Option<Scope> {
        let res = res.right_or_else(|resid| self.pkg.get_node(resid));

        match *res {
            Res::Def(kind, def) => kind.can_child().then_some(Scope { def, kind }),
            Res::PrimTy(_) | Res::Local(_) => None,
            Res::Unresolved => unreachable!(),
        }
    }

    /// Lookup in the package, at the given `scope` for `name` in the namespace
    /// `ns`.
    pub fn lookup_pkg(
        &mut self,
        scope: Scope,
        name: Symbol,
        expected_ns: Option<Namespace>,
    ) -> Option<(DefId, DefKind)> {
        let MaybeOwner::Owner(owner) = self.pkg.get_maybe(ItemId(scope.def)) else {
            return None;
        };

        let items = owner.items();
        let mut matching_items = Vec::with_capacity(6);

        for item_id in items {
            let item = self.pkg.get_item(*item_id);
            let defkind = item.defkind();

            if self.item_name(*item_id) == name {
                matching_items.push((*item_id, defkind));
            }
        }

        match *matching_items.as_slice() {
            [] => None,
            [(item_id, defkind)] => Some((item_id.0, defkind)),
            _ => {
                let mut matching_ns = Vec::new();

                for (item, defkind) in matching_items {
                    match expected_ns {
                        Some(expected_ns) if self.namespace_of_item(item) == expected_ns => {
                            matching_ns.push((item, defkind));
                        }
                        None => matching_ns.push((item, defkind)),
                        Some(_) => {}
                    }
                }

                if matching_ns.len() == 1 {
                    let (item_id, defkind) = matching_ns[0];

                    Some((item_id.0, defkind))
                } else {
                    unreachable!(
                        "can't have two items in the same scope and in the same namespace with the same name"
                    )
                }
            }
        }
    }

    /// Get the namespace of a resolution
    pub fn namespace_of_item(&mut self, item: ItemId) -> Namespace {
        let item = self.pkg.get_item(item);

        match item.kind {
            ItemKind::Fundef(_)
            | ItemKind::Fundecl(_)
            | ItemKind::Globdef(_)
            | ItemKind::Globdecl(_) => Namespace::Value,
            ItemKind::Directive(ref directive) => match directive {
                Directive::Mod(_, _) => Namespace::Type,
                Directive::Import { path, alias } => {
                    let path = self.get_node(*path);
                    dbg!(path);
                    dbg!(alias);
                    // todo!("NAMESPACE OF IMPORT");
                    Namespace::Type
                }
            },
        }
    }

    /// Tries to find a similar symbol in the current scope
    pub fn similar_in_scope(
        &self,
        name: Symbol,
        expected_ns: Namespace,
    ) -> Option<(Symbol, HirId<ResId>)> {
        for (type_entry, val_entry) in zip(&self.type_st.tables, &self.value_st.tables).rev() {
            match (
                suggest_similar(name, type_entry.entries.keys().copied()),
                suggest_similar(name, val_entry.entries.keys().copied()),
            ) {
                (Some(similar), None) => {
                    return Some((similar, type_entry.get(similar).unwrap()));
                }
                (None, Some(similar)) => {
                    return Some((similar, val_entry.get(similar).unwrap()));
                }
                (Some(similar_type), Some(similar_value)) => match expected_ns {
                    Namespace::Type => {
                        return Some((similar_type, type_entry.get(similar_type).unwrap()));
                    }
                    Namespace::Value => {
                        return Some((similar_value, val_entry.get(similar_value).unwrap()));
                    }
                },
                (None, None) => {}
            }
        }

        None
    }

    /// Resolves a path and return one candidate, this function will try to
    /// return something in the `expected_ns`.
    pub fn resolve_path(
        &mut self,
        path: PathId,
        expected_ns: Option<Namespace>,
    ) -> Result<Candidate, ResolveErr> {
        let Path {
            res: _,
            segments,
            span: _,
        } = self.mut_node(path);

        // get the initial candidates
        let mut seg_iter = segments.clone().into_iter();

        let Some(seg) = seg_iter.next() else {
            unreachable!();
        };

        let PathSegment {
            ident,
            id: _,
            res: _,
        } = {
            let hir_id = HirId {
                owner: self.cur,
                node_id: seg,
            };

            self.pkg.mut_node(hir_id)
        };
        let Identifier {
            name,
            span: name_span,
        } = *ident;

        // the current candidates
        let mut candidates: Vec<Candidate> = self
            .lookup(name)
            .present_items_ns()
            .map(|(res, ns)| {
                let child = self.child_scope(Either::Left(res));

                Candidate::new((res, self.pkg.get_node(res).clone()), ns, child)
            })
            .collect();

        if candidates.is_empty() {
            return Err(ResolveErr::NotFound {
                seg_span: name_span,
                similar: self.similar_not_found(expected_ns, name),
            });
        }

        // the next candidates
        let mut next: Vec<Candidate> = Vec::with_capacity(candidates.len());

        for seg in seg_iter {
            next.clear();
            let PathSegment {
                ident:
                    Identifier {
                        name,
                        span: name_span,
                    },
                id: _,
                res: seg_res,
            } = *{
                let hir_id = HirId {
                    owner: self.cur,
                    node_id: seg,
                };

                self.pkg.mut_node(hir_id)
            };

            for cand in &mut candidates {
                if let Some(child) = &cand.child
                    && let Some((defid, defkind)) =
                        self.lookup_pkg(child.clone(), name, expected_ns)
                {
                    let res = Res::Def(defkind, defid);
                    let child = self.child_scope(Either::Right(&res));

                    cand.push_res((seg_res, res), self.namespace_of_item(ItemId(defid)), child);
                    next.push(cand.clone());
                }
            }

            candidates = mem::take(&mut next);

            if candidates.is_empty() {
                return Err(ResolveErr::NotFound {
                    seg_span: name_span,
                    similar: self.similar_not_found(expected_ns, name),
                });
            }
        }

        match candidates.as_slice() {
            [] => unreachable!(),
            [cand] => Ok(cand.clone()),
            _ => {
                let mut matching_ns = Vec::new();

                for candidate in candidates {
                    match expected_ns {
                        Some(expected_ns) if candidate.ns == expected_ns => {
                            matching_ns.push(candidate);
                        }
                        Some(_) => {}
                        None => {
                            matching_ns.push(candidate);
                        }
                    }
                }

                match matching_ns.len() {
                    0 => unreachable!("or ambiguous idk"),
                    1 => Ok(matching_ns[0].clone()),
                    _ => Err(ResolveErr::Ambiguity {
                        candidates: matching_ns,
                    }),
                }
            }
        }
    }

    fn similar_not_found(
        &self,
        expected_ns: Option<Namespace>,
        name: Symbol,
    ) -> Option<(Symbol, Symbol)> {
        expected_ns.as_ref().and_then(|expected_ns| {
            if let Some((similar, res)) = self.similar_in_scope(name, *expected_ns) {
                let res = self.pkg.get_node(res);
                Some((similar, res.to_symbol()))
            } else {
                None
            }
        })
    }

    /// Apply a candidate to a path.
    pub fn apply_candidate(&mut self, path: PathId, cand: &Candidate) {
        let Path {
            res,
            ref segments,
            span: _,
        } = *self.get_node(path);

        debug_assert_eq!(segments.len(), cand.seg_res.len());

        for (seg_id, new_res) in zip(segments.clone(), cand.seg_res.clone()) {
            let PathSegment {
                ident: _,
                id: _,
                res,
            } = *self.get_node(seg_id);

            *self.pkg.mut_node(res) = new_res;
        }

        *self.pkg.mut_node(res) = cand.res.1.clone();
    }

    /// Renders a path to a string.
    pub fn render_path(&mut self, path: PathId) -> Result<String, fmt::Error> {
        let Path {
            res: _,
            segments,
            span: _,
        } = self.get_node(path);
        let mut res = String::with_capacity(segments.len() * 6); // heuristic

        for (i, seg) in segments.iter().enumerate() {
            let PathSegment {
                ident,
                id: _,
                res: _,
            } = self.get_node(*seg);

            write!(res, "{}", ident.name)?;

            if segments.len() - 1 != i {
                write!(res, "::")?;
            }
        }

        Ok(res)
    }

    /// Get the span of a resolution.
    pub fn res_span(&self, res: Either<HirId<ResId>, &Res>) -> Option<Span> {
        let res = res.right_or_else(|resid| self.pkg.get_node(resid));

        match *res {
            Res::Def(_, defid) => Some(self.pkg.get_item(ItemId(defid)).span),
            Res::PrimTy(_) => None,
            Res::Local(local) => {
                let Local { def, .. } = *self.pkg.get_node(local);

                Some(self.get_node(def).span())
            }
            Res::Unresolved => unreachable!(),
        }
    }

    /// Get the last segment name
    pub fn last_seg_name(&self, path: PathId) -> Symbol {
        let Path {
            res: _,
            segments,
            span: _,
        } = self.get_node(path);

        let last_seg = *segments
            .last()
            .expect("paths are always at least one segment long");

        self.get_node(last_seg).ident.name
    }

    /// Get the name of an item.
    pub fn item_name(&self, item_id: ItemId) -> Symbol {
        let item = self.pkg.get_item(item_id);

        match &item.kind {
            ItemKind::Fundef(fundef) => fundef.name.name,
            ItemKind::Fundecl(fundecl) => fundecl.name.name,
            ItemKind::Globdef(globdef) => globdef.name.name,
            ItemKind::Globdecl(globdecl) => globdecl.name.name,
            ItemKind::Directive(directive) => match directive {
                Directive::Mod(ident, _) => ident.name,
                Directive::Import { path, alias } => alias
                    .map(|ident| ident.name)
                    .unwrap_or_else(|| self.last_seg_name(*path)),
            },
        }
    }

    /// Create a new Resolution in the current owner. (Self::cur)
    fn mk_res(&mut self, res: Res) -> HirId<ResId> {
        HirId {
            owner: self.cur,
            node_id: self
                .pkg
                .mut_maybe(ItemId(self.cur.0))
                .unwrap_mut()
                .nodes
                .create(Node::Res(res))
                .to_res_id(),
        }
    }
}

impl<'hir> MutVisitor for Resolver<'hir> {
    const PREVISIT: bool = true;

    fn pkg(&mut self) -> &mut crate::hir::Package {
        self.pkg
    }

    fn cur(&mut self) -> &mut OwnerId {
        &mut self.cur
    }

    fn on_scope(&mut self, event: ScopeEvent) {
        match event {
            ScopeEvent::Enter => {
                self.enter_scope();
            }
            ScopeEvent::Leave => {
                self.leave_scope();
            }
        }
    }

    fn visit_mod(&mut self, defid: DefId) {
        self.super_mod(defid);
    }

    fn visit_ident(&mut self, ident: Identifier, ctx: DefContext) {
        let (res, ns) = match ctx {
            DefContext::Mod(defid) => (Res::Def(DefKind::Mod, defid), Namespace::Type),
            DefContext::Fundef(defid) => (Res::Def(DefKind::Fun, defid), Namespace::Value),
            DefContext::Fundecl(defid) => (Res::Def(DefKind::Fun, defid), Namespace::Value),
            DefContext::Globdef(defid) => (Res::Def(DefKind::Glob, defid), Namespace::Value),
            DefContext::Globdecl(defid) => (Res::Def(DefKind::Glob, defid), Namespace::Value),
            DefContext::Import(_) => {
                unreachable!()
            }
            DefContext::Local(local) => (Res::Local(local), Namespace::Value),
        };

        let res = self.mk_res(res);

        self.bind(ident.name, res, ns);
    }

    fn visit_path(&mut self, path: PathId, ctx: NameContext) {
        let expected_ns = match ctx {
            NameContext::Use(ns) => Some(ns),
            NameContext::Def(_) => None,
        };

        let candidate = match self.resolve_path(path, expected_ns) {
            Ok(cand) => cand,
            Err(ResolveErr::NotFound { seg_span, similar }) => {
                let Path {
                    res: _,
                    segments: _,
                    span: path_span,
                } = *self.get_node(path);

                let name = self
                    .render_path(path)
                    .expect("rendering the path is infallible");

                self.dcx.emit(NotFoundInScope {
                    seg_span,
                    path_span,
                    name,
                    similar,
                });

                return;
            }
            Err(ResolveErr::Ambiguity { candidates }) => {
                let Path {
                    res: _,
                    segments: _,
                    span: path_span,
                } = *self.get_node(path);

                let name = self
                    .render_path(path)
                    .expect("rendering the path is infallible");

                self.dcx.emit(AmbiguousName {
                    name,
                    primary: path_span,
                    defs: candidates
                        .iter()
                        .map(|cand| {
                            (
                                cand.res.1.to_symbol(),
                                self.res_span(Either::Right(&cand.res.1)),
                            )
                        })
                        .collect(),
                });

                return;
            }
        };

        self.apply_candidate(path, &candidate);

        match &ctx {
            NameContext::Use(_) => {}
            NameContext::Def(defctx) => {
                let DefContext::Import(alias) = defctx else {
                    unreachable!();
                };

                self.bind(
                    alias
                        .map(|ident| ident.name)
                        .unwrap_or_else(|| self.last_seg_name(path)),
                    candidate.res.0,
                    candidate.ns,
                );
            }
        }

        self.super_path(path, ctx);
    }
}

/// Namespace, stores names in scopes
#[derive(Clone)]
pub struct SymbolTable {
    tables: Vec<TableEntry>,
}

impl SymbolTable {
    /// Create a new namespace with an empty scope
    fn new() -> SymbolTable {
        SymbolTable::with_entry(TableEntry::new())
    }

    /// Creates a new namespace with `scope` as it's outer most scope.
    pub fn with_entry(scope: TableEntry) -> SymbolTable {
        SymbolTable {
            tables: vec![scope],
        }
    }

    /// Get the most inner scope.
    pub fn inner_entry(&self) -> &TableEntry {
        self.tables.last().expect("at least one scope")
    }

    /// Mutable `Self::inner_scope`.
    pub fn inner_mut(&mut self) -> &mut TableEntry {
        self.tables.last_mut().expect("at least one scope")
    }

    /// Enter a new scope
    pub fn enter_scope(&mut self) {
        self.tables.push(TableEntry::new());
    }

    /// Exit a scope
    pub fn exit_scope(&mut self) {
        assert!(self.tables.len() > 1, "can't exit out of the first scope");

        self.tables.pop();
    }

    /// Return the current scope level
    pub fn scope_level(&mut self) -> usize {
        self.tables.len() - 1
    }

    /// Lookup for the resolution of `name` in the inner most scope, returns
    /// `None` if `name` wasn't found.
    pub fn lookup_current(&self, name: Symbol) -> Option<HirId<ResId>> {
        self.inner_entry().get(name)
    }

    /// Lookup for the resolution of `name` starting from the inner most scope
    /// and goes on to the outer most scope, returns `None` if `name` wasn't
    /// found.
    pub fn lookup(&self, name: Symbol) -> Option<HirId<ResId>> {
        for table in self.tables.iter().rev() {
            if let Some(entry) = table.entries.get(&name) {
                return Some(entry.res);
            }
        }

        None
    }
}

impl fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.tables.iter().enumerate())
            .finish()
    }
}

/// Symbol table entry.
#[derive(Debug, Clone)]
pub struct Entry {
    pub res: HirId<ResId>,
    pub uses: u32,
}

impl Entry {
    /// Create an entry with zero uses.
    pub fn new(res: HirId<ResId>) -> Entry {
        Entry { res, uses: 0 }
    }

    /// Increment the uses counter by one, saturates at `u32::MAX`.
    pub fn increment_use(&mut self) {
        self.uses = self.uses.saturating_add(1);
    }
}

/// Symbol scope.
#[derive(Debug, Clone)]
pub struct TableEntry {
    entries: IndexMap<Symbol, Entry>,
}

impl TableEntry {
    /// Create a new empty table entry.
    fn new() -> TableEntry {
        TableEntry {
            entries: IndexMap::new(),
        }
    }

    /// Get the res mapped to the sym.
    pub fn get(&self, sym: Symbol) -> Option<HirId<ResId>> {
        self.entries.get(&sym).map(|entry| entry.res)
    }
}

impl FromIterator<(Symbol, HirId<ResId>)> for TableEntry {
    fn from_iter<T: IntoIterator<Item = (Symbol, HirId<ResId>)>>(iter: T) -> Self {
        TableEntry {
            entries: IndexMap::from_iter(
                iter.into_iter()
                    .map(|(sym, res)| (sym, Entry { res, uses: 0 })),
            ),
        }
    }
}

/// A resolution candidate.
#[derive(Debug, Clone)]
pub struct Candidate {
    /// the resolution, the same as the last of `seg_res`.
    ///
    /// `.0` is where to update the res and `.1` is what will be the updated
    /// value after applying it.
    pub res: (HirId<ResId>, Res),
    /// the namespace of this resolution
    pub ns: Namespace,
    /// the child scope of this candidate
    pub child: Option<Scope>,
    /// the new resolutions of the segments in the same order
    pub seg_res: Vec<Res>,
}

impl Candidate {
    /// Create a new candidate
    pub fn new(res: (HirId<ResId>, Res), ns: Namespace, child: Option<Scope>) -> Candidate {
        Candidate {
            res: res.clone(),
            ns,
            child,
            seg_res: vec![res.1],
        }
    }

    /// Push a resolution to the candidate
    pub fn push_res(&mut self, res: (HirId<ResId>, Res), ns: Namespace, child: Option<Scope>) {
        self.res = res.clone();
        self.ns = ns;
        self.seg_res.push(res.1);
        self.child = child;
    }
}

/// Resolve error.
#[derive(Debug, Clone)]
pub enum ResolveErr {
    NotFound {
        /// the span of the segment that is responsible for the failure
        seg_span: Span,
        /// not found but something similar was found.
        ///
        /// `.0` is the similar name
        /// `.1` is what it is
        similar: Option<(Symbol, Symbol)>,
    },
    Ambiguity {
        /// all the candidates that are ambiguous.
        candidates: Vec<Candidate>,
    },
}
