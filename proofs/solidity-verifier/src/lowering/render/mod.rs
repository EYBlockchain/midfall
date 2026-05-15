// SPDX-License-Identifier: CC0-1.0
//! Rendering data models and Yul formatting hooks.
//!
//! Rendering is deliberately the last step: callers pass already-planned
//! calldata, layout, VK, KZG, and quotient facts into simple Askama models so
//! templates stay declarative.

pub(crate) mod models;
pub(crate) mod yul;

pub(crate) use models::*;
