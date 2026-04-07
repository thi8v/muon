//! Name resolution of HIR, the next stage after lowering.

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
    visit::{DefContext, MutVisitor, NameContext, Namespace, PerNS},
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
        let mut outer_ts =
            TableEntry::from_iter(category_iter(categories::PRIMITIVE_RANGE).map(|sym| {
                (
                    sym,
                    Res::from(PrimTy::from_symbol(sym).expect("the iterator is messed up")),
                )
            }));

        outer_ts
            .map
            .insert(sym::Pkg, Res::Def(DefKind::Mod, DefId::PACKAGE_DEF));

        let type_ns = SymbolTable::with_scope(outer_ts);

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
    pub fn lookup(&mut self, name: Symbol) -> PerNS<Option<Res>> {
        PerNS {
            type_ns: self.type_st.lookup(name),
            value_ns: self.value_st.lookup(name),
        }
    }

    /// Bind `name` to `res` in the namespace `ns` at the current scope.
    pub fn bind(&mut self, name: Symbol, res: Res, ns: Namespace) {
        let symtable = match ns {
            Namespace::Type => &mut self.type_st,
            Namespace::Value => &mut self.value_st,
        };

        if let Some(old_res) = symtable.lookup(name)
            && !self.can_shadow(&res, &old_res)
        {
            self.dcx.emit(NameDefinedMultipleTimes {
                name,
                new_span: self.res_span(&res).expect("a definition always has a span"),
                old_span: self
                    .res_span(&old_res)
                    .expect("a definition always has a span"),
            });
            return;
        }

        // reborrow because borrow checker is annoying
        let symtable = match ns {
            Namespace::Type => &mut self.type_st,
            Namespace::Value => &mut self.value_st,
        };

        symtable.inner_mut().map.insert(name, res);
    }

    /// Returns `true` if `new` can shadow `old`.
    pub fn can_shadow(&self, new: &Res, old: &Res) -> bool {
        // NOTE: for now it's super simple shadowing rules but it may be broaden
        // later.

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
        let hir_id = HirId {
            owner: self.cur,
            node_id: id,
        };

        self.pkg.get_node(hir_id)
    }

    /// Mutable `get_node`.
    pub fn mut_node<Id: NodeType>(&mut self, id: Id) -> &mut Id::NodeTy {
        let hir_id = HirId {
            owner: self.cur,
            node_id: id,
        };

        self.pkg.mut_node(hir_id)
    }

    /// Get the scope of the childs.
    pub fn child_scope(&mut self, res: &Res) -> Option<Scope> {
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
        expected_ns: Namespace,
    ) -> Option<(DefId, DefKind)> {
        let MaybeOwner::Owner(owner) = self.pkg.get_maybe(ItemId(scope.def)) else {
            return None;
        };

        let items = owner.items();
        let mut matching_items = Vec::with_capacity(6);

        for item_id in items {
            let item = self.pkg.get_item(*item_id);
            let defkind = item.defkind();

            if let Some(item_name) = item.name()
                && item_name == name
            {
                matching_items.push((*item_id, defkind));
            }
        }

        match *matching_items.as_slice() {
            [] => None,
            [(item_id, defkind)] => Some((item_id.0, defkind)),
            _ => {
                let mut matching_ns = Vec::new();

                for (item, defkind) in matching_items {
                    if self.namespace_of_item(item) == expected_ns {
                        matching_ns.push((item, defkind));
                    }
                }

                if matching_ns.len() == 1 {
                    let (item_id, defkind) = matching_ns[0];

                    Some((item_id.0, defkind))
                } else {
                    // TODO: i don't know how to handle ambiguity right now so
                    // it panics right now.
                    todo!("AMBIGUITY")
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
            ItemKind::Extern(_) => Namespace::Type,
            ItemKind::Directive(ref directive) => match directive {
                Directive::Mod(_, _) => Namespace::Type,
                Directive::Import { .. } => todo!("NS OF IMPORT"),
            },
        }
    }

    /// Tries to find a similar symbol in the current scope
    pub fn similar_in_scope(
        &mut self,
        name: Symbol,
        expected_ns: Namespace,
    ) -> Option<(Symbol, &Res)> {
        for (type_entry, val_entry) in zip(&self.type_st.entries, &self.value_st.entries).rev() {
            match (
                suggest_similar(name, type_entry.map.keys().copied()),
                suggest_similar(name, val_entry.map.keys().copied()),
            ) {
                (Some(similar), None) => {
                    return Some((similar, type_entry.map.get(&similar).unwrap()));
                }
                (None, Some(similar)) => {
                    return Some((similar, val_entry.map.get(&similar).unwrap()));
                }
                (Some(similar_type), Some(similar_value)) => match expected_ns {
                    Namespace::Type => {
                        return Some((similar_type, type_entry.map.get(&similar_type).unwrap()));
                    }
                    Namespace::Value => {
                        return Some((similar_value, val_entry.map.get(&similar_value).unwrap()));
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
        expected_ns: Namespace,
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
                let child = self.child_scope(&res);

                Candidate::new(res, ns, child)
            })
            .collect();

        if candidates.is_empty() {
            return Err(ResolveErr::NotFound {
                seg_span: name_span,
                similar: self
                    .similar_in_scope(name, expected_ns)
                    .map(|(similar, res)| (similar, res.to_symbol())),
            });
        }

        // the next candidates
        let mut next: Vec<Candidate> = Vec::with_capacity(candidates.len());

        for seg in seg_iter {
            next.clear();
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

            for cand in &mut candidates {
                if let Some(child) = &cand.child
                    && let Some((defid, defkind)) =
                        self.lookup_pkg(child.clone(), name, expected_ns)
                {
                    let res = Res::Def(defkind, defid);
                    let child = self.child_scope(&res);

                    cand.push_res(res, self.namespace_of_item(ItemId(defid)), child);
                    next.push(cand.clone());
                }
            }

            candidates = mem::take(&mut next);

            if candidates.is_empty() {
                return Err(ResolveErr::NotFound {
                    seg_span: name_span,
                    similar: self
                        .similar_in_scope(name, expected_ns)
                        .map(|(similar, res)| (similar, res.to_symbol())),
                });
            }
        }

        match candidates.as_slice() {
            [] => unreachable!(),
            [cand] => Ok(cand.clone()),
            _ => {
                let mut matching_ns = Vec::new();

                for candidate in candidates {
                    if candidate.ns == expected_ns {
                        matching_ns.push(candidate);
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

    /// Apply a candidate to a path.
    pub fn apply_candidate(&mut self, path: PathId, cand: Candidate) {
        let Path {
            res,
            segments,
            span: _,
        } = self.mut_node(path);

        *res = cand.res;

        debug_assert_eq!(segments.len(), cand.seg_res.len());

        for (seg_id, new_res) in zip(segments.clone(), cand.seg_res) {
            let PathSegment {
                ident: _,
                id: _,
                res,
            } = self.mut_node(seg_id);

            *res = new_res;
        }
    }

    /// Renders a path to a string.
    pub fn render_path(&mut self, path: PathId) -> Result<String, fmt::Error> {
        let Path {
            res: _,
            segments,
            span: _,
        } = self.get_node(path);
        let mut res = String::with_capacity(segments.len() * 6); // euristic

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
    pub fn res_span(&self, res: &Res) -> Option<Span> {
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
}

impl<'hir> MutVisitor for Resolver<'hir> {
    fn pkg(&mut self) -> &mut crate::hir::Package {
        self.pkg
    }

    fn cur(&mut self) -> &mut OwnerId {
        &mut self.cur
    }

    fn visit_mod(&mut self, defid: DefId) {
        self.enter_scope(); // mod scope

        self.super_mod(defid);

        self.leave_scope(); // mod scope
    }

    fn visit_ident(&mut self, ident: Identifier, ctx: DefContext) {
        match ctx {
            DefContext::Mod(defid) => {
                self.bind(ident.name, Res::Def(DefKind::Mod, defid), Namespace::Type);
            }
            DefContext::Fundef(defid) => {
                self.bind(ident.name, Res::Def(DefKind::Fun, defid), Namespace::Value);
            }
            DefContext::Fundecl(defid) => {
                self.bind(ident.name, Res::Def(DefKind::Fun, defid), Namespace::Value);
            }
            DefContext::Globdef(defid) => {
                self.bind(ident.name, Res::Def(DefKind::Glob, defid), Namespace::Value);
            }
            DefContext::Globdecl(defid) => {
                self.bind(ident.name, Res::Def(DefKind::Glob, defid), Namespace::Value);
            }
            DefContext::Import(vis, alias) => {
                _ = vis;
                _ = alias;

                todo!("IMPORT")
            }
            DefContext::Local(local) => {
                self.bind(ident.name, Res::Local(local), Namespace::Value);
            }
        }
    }

    fn visit_path(&mut self, path: PathId, ctx: NameContext) {
        match &ctx {
            NameContext::Use(ns) => {
                let candidate = match self.resolve_path(path, *ns) {
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
                                .map(|cand| (cand.res.to_symbol(), self.res_span(&cand.res)))
                                .collect(),
                        });

                        return;
                    }
                };

                self.apply_candidate(path, candidate);
            }
            NameContext::Def(_) => {
                // TODO: ...
            }
        }

        self.super_path(path, ctx);
    }
}

/// Namespace, stores names in scopes
#[derive(Clone)]
pub struct SymbolTable {
    entries: Vec<TableEntry>,
}

impl SymbolTable {
    /// Create a new namespace with an empty scope
    pub fn new() -> SymbolTable {
        SymbolTable::with_scope(TableEntry::new())
    }

    /// Creates a new namespace with `scope` as it's outer most scope.
    pub fn with_scope(scope: TableEntry) -> SymbolTable {
        SymbolTable {
            entries: vec![scope],
        }
    }

    /// Get the most inner scope.
    pub fn inner_scope(&self) -> &TableEntry {
        self.entries.last().expect("at least one scope")
    }

    /// Mutable `Self::inner_scope`.
    pub fn inner_mut(&mut self) -> &mut TableEntry {
        self.entries.last_mut().expect("at least one scope")
    }

    /// Enter a new scope
    pub fn enter_scope(&mut self) {
        self.entries.push(TableEntry::new());
    }

    /// Exit a scope
    pub fn exit_scope(&mut self) {
        assert!(self.entries.len() > 1, "can't exit out of the first scope");

        self.entries.pop();
    }

    /// Return the current scope level
    pub fn scope_level(&mut self) -> usize {
        self.entries.len() - 1
    }

    /// Lookup for the resolution of `name` in the inner most scope, returns
    /// `None` if `name` wasn't found.
    pub fn lookup_current(&self, name: Symbol) -> Option<Res> {
        self.inner_scope().map.get(&name).cloned()
    }

    /// Lookup for the resolution of `name` starting from the inner most scope
    /// and goes on to the outer most scope, returns `None` if `name` wasn't
    /// found.
    pub fn lookup(&self, name: Symbol) -> Option<Res> {
        for entry in self.entries.iter().rev() {
            if let Some(res) = entry.map.get(&name) {
                return Some(res.clone());
            }
        }

        None
    }
}

impl fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.entries.iter().enumerate())
            .finish()
    }
}

/// Symbol scope.
#[derive(Debug, Clone)]
pub struct TableEntry {
    map: IndexMap<Symbol, Res>,
}

impl TableEntry {
    /// Create a new empty table entry.
    pub fn new() -> TableEntry {
        TableEntry {
            map: IndexMap::new(),
        }
    }
}

impl FromIterator<(Symbol, Res)> for TableEntry {
    fn from_iter<T: IntoIterator<Item = (Symbol, Res)>>(iter: T) -> Self {
        TableEntry {
            map: IndexMap::from_iter(iter),
        }
    }
}

/// A resolution candidate.
#[derive(Debug, Clone)]
pub struct Candidate {
    /// the resolution, the same as the last of `seg_res`.
    pub res: Res,
    /// the namespace of this resolution
    pub ns: Namespace,
    /// the child scope of this candidate
    pub child: Option<Scope>,
    /// the new resolutions of the segments in the same order
    pub seg_res: Vec<Res>,
}

impl Candidate {
    /// Create a new candidate
    pub fn new(res: Res, ns: Namespace, child: Option<Scope>) -> Candidate {
        Candidate {
            res: res.clone(),
            ns,
            child,
            seg_res: vec![res],
        }
    }

    /// Push a resolution to the candidate
    pub fn push_res(&mut self, res: Res, ns: Namespace, child: Option<Scope>) {
        self.res = res.clone();
        self.ns = ns;
        self.seg_res.push(res);
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
