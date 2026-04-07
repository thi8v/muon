//! Definition id, used from HIR to the end

use muonc_entity::{EntityMap, entity};

entity! {
    /// Definition Id, uniquely identifies an item in the package being compiled
    pub struct DefId {
        /// The module definition of the root of the package (always 0).
        const PACKAGE_DEF = 0;
    }
}

pub type DefMap<T> = EntityMap<DefId, T>;
