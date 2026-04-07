//! High-level Intermediate Representation of Muon
//!
//! # Overview
//!
//! This stage is used to perform multiple things: resolve the names, desugar
//! some of the syntax and expand the module declaration.
//!
//! # Stages
//!
//! * Lower with `LoweringCtx`.
//! * Resolve with `Resolver`.

pub mod diags;
pub mod hir;
pub mod lowering;
pub mod pretty;
pub mod resolve;
pub mod visit;
