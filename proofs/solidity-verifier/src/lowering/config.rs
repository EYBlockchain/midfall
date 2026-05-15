// SPDX-License-Identifier: CC0-1.0
//! Constants for the generated verifier shape used by the IVC Solidity bench.
//!
//! The generator intentionally emits one shape: a compact byte-oriented
//! quotient VM with a small direct prefix, selected native callbacks, native
//! permutation/lookup families, structured trash suffix, and limb-aware VM
//! opcodes.

// Keep a small direct prefix as the default gas-capped compact VM path:
// it avoids running the entire numerator through the interpreter while staying
// below the external quotient evaluator size budget.
pub(crate) const DEFAULT_HYBRID_QUOTIENT_INLINE_IDENTITIES: usize = 4;

// Spend a bounded slice of quotient-evaluator bytecode headroom on native VM
// callbacks. After the direct prefix, up to N remaining gate identities are
// emitted as VM opcodes that call generated Yul blocks; everything else stays
// in the compact interpreter. Selection is a gas/byte knapsack under an
// estimated native callback byte budget.
pub(crate) const DEFAULT_QUOTIENT_NATIVE_GATES: usize = 4;
// The compact quotient VM path is the default size-oriented emitter: it stores
// identity arithmetic as data in the VK and interprets it from one small Yul
// loop. Emit the final trash suffix as structured Yul by default to save
// dispatch gas.
// Limb-aware VM superinstructions are part of the default byte-oriented
// pinned-VK lowering: they structurally compress recurring 7-limb
// foreign-field expressions while preserving the compact quotient interpreter.
pub(crate) const DEFAULT_QUOTIENT_LIMB_VM_OPS: bool = true;
