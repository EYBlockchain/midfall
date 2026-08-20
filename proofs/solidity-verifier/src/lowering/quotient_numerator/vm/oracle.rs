// SPDX-License-Identifier: CC0-1.0
//! Frame-backed expression oracle for the compiled-artifact quotient
//! differential (audit finding F1).
//!
//! [`super::certify`] proves bytecode/expression agreement for identities the
//! compact VM interprets, but stops at the bytecode boundary: inline gates,
//! native gate callbacks, the structured permutation/LogUp kernels, and the
//! trash tail are certified positionally only. This module supplies the
//! host-side half of a differential that extends the same Schwartz–Zippel
//! argument past that boundary to the solc-compiled evaluator: it folds every
//! identity expression tree over a flat pseudorandom memory frame so the
//! result can be compared word-for-word against the deployed
//! `Halo2QuotientEvaluator` running the exact same frame.
//!
//! Honest scope: for permutation, lookup, and trash identities the oracle
//! expressions are re-parsed from the emitter's own straight-line Yul
//! (`quotient_yul_expr`), so this differential certifies the structural
//! loop/table/chunking restructuring and the solc-compiled execution — *not*
//! the per-identity formula, whose independent leg stays with the
//! `rust-verifier-trace` proof differential against midnight-proofs. Gate
//! identities (inline, native callbacks, and interpreted) have genuinely
//! independent typed lowering from `vk.cs().gates()`, so for them the
//! differential is a full independent check.
//!
//! This module is deliberately free of solc/revm imports so a future opt-in
//! render-time gate can promote it by changing only the `cfg` on the module
//! declaration.

use std::collections::HashMap;

use ff::{Field, FromUniformBytes, PrimeField};
use midnight_curves::Fq;
use sha3::{Digest, Keccak256};

use super::{quotient_fq_from_u256, QuotientExpr, QuotientIdentity, QuotientMem, QuotientTarget};
use crate::lowering::{encoding::fe_to_u256, layout::WORD_BYTES, render::QuotientExternal};

/// Domain tag for pseudorandom frame words, keyed by `(seed, address)`.
const QUOTIENT_FRAME_WORD_DOMAIN: &[u8] = b"midfall/quotient-vm/frame-differential/v1";
/// Domain tag for per-iteration frame seeds derived from an artifact-bound
/// base seed.
const QUOTIENT_FRAME_SEED_DOMAIN: &[u8] = b"midfall/quotient-vm/frame-differential-seed/v1";

/// Memory backing for direct quotient-expression evaluation.
///
/// The `&mut self` receivers keep the trait compatible with caching
/// implementations shaped like [`super::reference::QuotientRefMemory`].
pub(crate) trait QuotientOracleMemory {
    /// Value at an absolute verifier memory pointer.
    fn load(&mut self, ptr: u32) -> Fq;
    /// Value behind a symbolic memory token, optionally offset.
    fn token(&mut self, token: u8, offset: u32) -> Fq;
}

/// Literal-pointer-only memory used by the lowering unit tests.
///
/// Token loads panic, preserving the existing literal-only test contract: a
/// unit fixture that suddenly needs a token resolves addresses it never
/// declared, which is a test bug, not an evaluation strategy.
impl QuotientOracleMemory for HashMap<u32, Fq> {
    fn load(&mut self, ptr: u32) -> Fq {
        self[&ptr]
    }

    fn token(&mut self, _token: u8, _offset: u32) -> Fq {
        panic!("test expressions use literal memory only")
    }
}

/// Evaluate the typed quotient expression tree against oracle memory.
pub(crate) fn eval_quotient_expr_with(
    expr: &QuotientExpr,
    mem: &mut impl QuotientOracleMemory,
) -> Fq {
    match expr {
        QuotientExpr::Const(value) => quotient_fq_from_u256(*value)
            .expect("quotient expression constants are canonical field elements"),
        QuotientExpr::Mem(QuotientMem::Literal(ptr)) => mem.load(*ptr),
        QuotientExpr::Mem(QuotientMem::Token(token)) => mem.token(*token, 0),
        QuotientExpr::Mem(QuotientMem::TokenOffset(token, offset)) => mem.token(*token, *offset),
        QuotientExpr::Add(lhs, rhs) => {
            eval_quotient_expr_with(lhs, mem) + eval_quotient_expr_with(rhs, mem)
        }
        QuotientExpr::Mul(lhs, rhs) => {
            eval_quotient_expr_with(lhs, mem) * eval_quotient_expr_with(rhs, mem)
        }
        QuotientExpr::Neg(inner) => -eval_quotient_expr_with(inner, mem),
    }
}

/// One identity's directly evaluated value and its y-batch position.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QuotientIdentityTraceEntry {
    /// Position in the global y-batch.
    pub(crate) global_index: usize,
    /// Accumulator target for this identity.
    pub(crate) target: QuotientTarget,
    /// Directly evaluated identity value.
    pub(crate) value: Fq,
    /// Power of `y` applied to this identity in the final scalars.
    pub(crate) y_power: usize,
}

/// Expected linearization outputs for one memory assignment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct QuotientLinearizationArtifacts {
    /// Per-identity values in the order the identities were supplied.
    pub(crate) identity_trace: Vec<QuotientIdentityTraceEntry>,
    /// y-batched numerator over `Main`-target identities.
    pub(crate) main_numerator: Fq,
    /// y-batched selector accumulators, indexed by sorted-selector position.
    pub(crate) selector_buckets: Vec<Fq>,
    /// The verifier-facing scalar `-nu_y(x)`.
    pub(crate) quotient_expected_eval: Fq,
}

/// Small exponentiation helper for expected linearization powers.
pub(crate) fn fq_pow(base: Fq, exp: usize) -> Fq {
    (0..exp).fold(Fq::ONE, |acc, _| acc * base)
}

/// Evaluate expected quotient linearization artifacts directly from
/// identities.
pub(crate) fn expected_linearization_artifacts(
    identities: &[QuotientIdentity],
    mem: &mut impl QuotientOracleMemory,
    y: Fq,
    selector_count: usize,
) -> QuotientLinearizationArtifacts {
    let mut identity_trace = Vec::with_capacity(identities.len());
    let mut main_numerator = Fq::ZERO;
    let mut selector_buckets = vec![Fq::ZERO; selector_count];
    let total = identities.len();

    for identity in identities {
        let value = eval_quotient_expr_with(&identity.expr, mem);
        let y_power = total - 1 - identity.meta.global_index;
        let scaled = value * fq_pow(y, y_power);
        match identity.target {
            QuotientTarget::Main => main_numerator += scaled,
            QuotientTarget::Selector(selector_idx) => selector_buckets[selector_idx] += scaled,
        }
        identity_trace.push(QuotientIdentityTraceEntry {
            global_index: identity.meta.global_index,
            target: identity.target,
            value,
            y_power,
        });
    }

    QuotientLinearizationArtifacts {
        identity_trace,
        main_numerator,
        selector_buckets,
        quotient_expected_eval: -main_numerator,
    }
}

/// Oracle memory that reads the exact byte frame handed to the compiled
/// evaluator.
///
/// Both sides of the frame differential observe the same words by
/// construction; a wrong-slot bug on either side shows up as a value mismatch
/// under the pseudorandom assignment.
#[derive(Debug)]
pub(crate) struct QuotientFrameMemory<'a> {
    frame: &'a [u8],
    frame_base: usize,
    /// `[start, end)` byte range of the VK payload inside verifier memory.
    vk_window: core::ops::Range<usize>,
    token_bases: &'a [(u8, usize)],
}

impl<'a> QuotientFrameMemory<'a> {
    /// Wrap one built frame with the layout facts needed to resolve loads.
    pub(crate) fn new(
        frame: &'a [u8],
        frame_base: usize,
        vk_window: core::ops::Range<usize>,
        token_bases: &'a [(u8, usize)],
    ) -> Self {
        Self {
            frame,
            frame_base,
            vk_window,
            token_bases,
        }
    }
}

impl QuotientOracleMemory for QuotientFrameMemory<'_> {
    fn load(&mut self, ptr: u32) -> Fq {
        let addr = ptr as usize;
        let offset = addr.checked_sub(self.frame_base).unwrap_or_else(|| {
            panic!(
                "quotient frame oracle load at {addr:#x} is below the frame base {:#x}",
                self.frame_base
            )
        });
        assert!(
            offset + WORD_BYTES <= self.frame.len(),
            "quotient frame oracle load at {addr:#x} reads past the frame end {:#x}",
            self.frame_base + self.frame.len()
        );
        let mut le = [0u8; WORD_BYTES];
        for (le_byte, be_byte) in
            le.iter_mut().zip(self.frame[offset..offset + WORD_BYTES].iter().rev())
        {
            *le_byte = *be_byte;
        }
        if let Some(value) = Option::<Fq>::from(Fq::from_repr(<Fq as PrimeField>::Repr::from(le))) {
            return value;
        }
        // Non-canonical words are legal only inside the VK payload (packed
        // program bytes and EIP-2537 point encodings), which the oracle
        // expressions never reference. The mod-r reduction below is a safety
        // net for those, not a semantic equivalence claim: EVM `sub(r, x)` on
        // a non-canonical word diverges from Fr negation, so an expression
        // reaching one must fail the differential loudly here instead.
        debug_assert!(
            self.vk_window.contains(&addr),
            "non-canonical frame word loaded at {addr:#x}, outside the VK payload window \
             {:#x}..{:#x}",
            self.vk_window.start,
            self.vk_window.end
        );
        let mut wide = [0u8; 2 * WORD_BYTES];
        wide[..WORD_BYTES].copy_from_slice(&le);
        <Fq as FromUniformBytes<64>>::from_uniform_bytes(&wide)
    }

    fn token(&mut self, token: u8, offset: u32) -> Fq {
        let base = self
            .token_bases
            .iter()
            .find_map(|(candidate, base)| (*candidate == token).then_some(*base))
            .unwrap_or_else(|| {
                panic!("quotient frame oracle has no base for memory token {token:#x}")
            });
        let base = u32::try_from(base).expect("token base address fits in u32");
        self.load(base + offset)
    }
}

/// Build one pseudorandom evaluator frame with the genuine VK payload
/// overlaid.
///
/// Every 32-byte word at absolute address `a` is a canonical Fr element
/// derived from `(seed, a)`, so the assignment breaks the value correlations
/// honest proofs satisfy (chunk-boundary products, boundary constraints) and
/// wrong-slot bugs cannot cancel. The VK subrange must be genuine — it carries
/// the const table and packed bytecode the evaluator's VM executes.
/// `LINEARIZATION_EVAL_MPTR` is deliberately not special-cased: it is a write
/// target the oracle never reads, so leaving it random freely detects a
/// missing write.
pub(crate) fn build_quotient_frame(
    external: &QuotientExternal,
    vk_mptr: usize,
    vk_bytes: &[u8],
    seed: [u8; 32],
) -> Vec<u8> {
    assert!(
        external.frame_len.is_multiple_of(WORD_BYTES),
        "quotient frame length {:#x} is not word-aligned",
        external.frame_len
    );
    let mut frame = vec![0u8; external.frame_len];
    for word_index in 0..external.frame_len / WORD_BYTES {
        let addr = external.frame_base + word_index * WORD_BYTES;
        let value = derive_frame_word(seed, addr);
        let be = fe_to_u256::<Fq>(&value).to_be_bytes::<32>();
        frame[word_index * WORD_BYTES..(word_index + 1) * WORD_BYTES].copy_from_slice(&be);
    }

    let vk_offset = vk_mptr
        .checked_sub(external.frame_base)
        .expect("VK payload starts inside the quotient frame");
    assert!(
        vk_offset + vk_bytes.len() <= frame.len(),
        "VK payload ends inside the quotient frame"
    );
    frame[vk_offset..vk_offset + vk_bytes.len()].copy_from_slice(vk_bytes);
    frame
}

/// Derive one canonical frame word from its absolute address.
///
/// Mirrors `QuotientRefMemory::derive`: two chained keccaks widen the digest
/// to 64 uniform bytes so the sampled Fr value is unbiased.
fn derive_frame_word(seed: [u8; 32], address: usize) -> Fq {
    let mut hasher = Keccak256::new();
    hasher.update(QUOTIENT_FRAME_WORD_DOMAIN);
    hasher.update(seed);
    hasher.update((address as u64).to_be_bytes());
    let lo = hasher.finalize();

    let mut hasher = Keccak256::new();
    hasher.update(QUOTIENT_FRAME_WORD_DOMAIN);
    hasher.update(b"/hi");
    hasher.update(lo);
    let hi = hasher.finalize();

    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(&lo);
    wide[32..].copy_from_slice(&hi);
    <Fq as FromUniformBytes<64>>::from_uniform_bytes(&wide)
}

/// Derive the per-iteration frame seed from an artifact-bound base seed.
///
/// The base is expected to come from `certify::derive_certify_seed` over the
/// finalized build, every surface's expression tree, and the VK payload, so
/// the sampled assignment is fixed only after all compared artifacts are.
pub(crate) fn frame_differential_seed(base: [u8; 32], iteration: u64) -> [u8; 32] {
    let mut hasher = Keccak256::new();
    hasher.update(QUOTIENT_FRAME_SEED_DOMAIN);
    hasher.update(base);
    hasher.update(iteration.to_be_bytes());
    hasher.finalize().into()
}
