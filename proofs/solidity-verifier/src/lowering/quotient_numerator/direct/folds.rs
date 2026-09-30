// SPDX-License-Identifier: CC0-1.0
//! Code-generation-time structural check of the direct lowering's `y`-batch
//! fold.
//!
//! Every fold statement of a direct render,
//!
//! ```text
//! mstore(B, addmod(mload(B), mulmod(mload(W), e, r), r))
//! ```
//!
//! is rendered from a [`FoldSite`] by [`FoldSite::statement`]; loops that
//! contain fold sites render their `for` header from the same [`FoldLoop`]
//! record. The emitters (gate identity functions, and the structured
//! permutation / lookup / trash emitters under `StructuredFold::Weighted`)
//! record each site together with a [`FoldLabel`]: the identity the code at
//! that site computes, named by *what it is* (gate and polynomial, "product
//! identity of permutation set s", "helper of chunk c of lookup l", ...),
//! independently of the index arithmetic that picked its weight. The section
//! records how many times it calls each function.
//!
//! [`check`] expands every site (loops iteration by iteration, with the weight
//! address `YP_k0 - 32 v` of iteration `v`), maps each label to its manifest
//! entry through the canonical family orders of
//! `proofs/src/plonk/{permutation,logup}.rs`, and proves that
//!
//! * every identity `j` in `0..m` is folded exactly once,
//! * with weight `Y_POW[m-1-j]` (`compute_linearization_commitment`),
//! * into the bucket its manifest target names (`Q_BUCKET_s` at
//!   `SELECTOR_ACC_MPTR + 32 s` for simple-selector column
//!   `simple_selector_cols[s]`, `Q_MAIN_ACC` for fully evaluated identities),
//! * and that no weight is used twice and none is unused.
//!
//! It checks where and how each identity value is folded, not how the value
//! is computed: the identity bodies are covered by translation validation
//! (IR level, `validate.rs`) and by the EVM probe tests (emitted Yul).

use std::collections::BTreeMap;

use crate::api::{
    QuotientIdentityManifest, QuotientIdentityManifestTarget, QuotientIdentitySource,
};
use crate::lowering::layout::WORD_BYTES;

/// Accumulator word a fold site adds into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FoldBucket {
    /// `Q_MAIN_ACC`: fully evaluated identities (negated into
    /// `QUOTIENT_EVAL_MPTR` at the end of the section).
    Main,
    /// `Q_BUCKET_s`: simple-selector bucket `s`.
    Selector(usize),
}

impl FoldBucket {
    /// Yul name of the bucket word.
    pub(crate) fn name(self) -> String {
        match self {
            Self::Main => "Q_MAIN_ACC".to_string(),
            Self::Selector(s) => format!("Q_BUCKET_{s}"),
        }
    }
}

/// The identity a fold site folds, named by what its code computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FoldLabel {
    /// `cs.gates()[gate_index].polynomials()[polynomial_index]`.
    Gate {
        gate_index: usize,
        polynomial_index: usize,
    },
    /// `l_0 * (1 - z_0)`.
    PermutationFirstBoundary,
    /// `l_last * (z_l^2 - z_l)`.
    PermutationLastBoundary,
    /// `l_0 * (z_set - z_{set-1}(omega^last))`, `set >= 1`.
    PermutationContinuity { set: usize },
    /// Active-row product identity of permutation set `set`.
    PermutationProduct { set: usize },
    /// `(l_0 + l_last) * Z` of lookup `lookup`.
    LookupBoundary { lookup: usize },
    /// Helper identity of input chunk `chunk` of lookup `lookup`.
    LookupHelper { lookup: usize, chunk: usize },
    /// Accumulator identity of lookup `lookup`.
    LookupAccumulator { lookup: usize },
    /// Trash argument `index`.
    Trash { index: usize },
}

impl std::fmt::Display for FoldLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Gate {
                gate_index,
                polynomial_index,
            } => write!(f, "gate {gate_index} polynomial {polynomial_index}"),
            Self::PermutationFirstBoundary => write!(f, "permutation first-set boundary"),
            Self::PermutationLastBoundary => write!(f, "permutation last-set boundary"),
            Self::PermutationContinuity { set } => {
                write!(f, "permutation continuity of set {set}")
            }
            Self::PermutationProduct { set } => write!(f, "permutation product of set {set}"),
            Self::LookupBoundary { lookup } => write!(f, "lookup {lookup} boundary"),
            Self::LookupHelper { lookup, chunk } => {
                write!(f, "lookup {lookup} helper of chunk {chunk}")
            }
            Self::LookupAccumulator { lookup } => write!(f, "lookup {lookup} accumulator"),
            Self::Trash { index } => write!(f, "trash argument {index}"),
        }
    }
}

/// A Yul loop `for { let var := start } lt(var, end) { var := add(var, 1) }`
/// around fold sites. Its header is rendered from this record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FoldLoop {
    pub(crate) var: &'static str,
    pub(crate) start: usize,
    pub(crate) end: usize,
}

impl FoldLoop {
    /// The loop header, up to and including the body's opening brace.
    pub(crate) fn header(&self) -> String {
        let v = self.var;
        format!(
            "for {{ let {v} := {} }} lt({v}, {}) {{ {v} := add({v}, 1) }} {{",
            self.start, self.end
        )
    }
}

/// Weight operand of a fold statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FoldWeight {
    /// `mload(YP_k)`.
    Fixed(usize),
    /// `mload(sub(YP_k0, shl(5, var)))` inside a loop over `var`.
    LoopDown { k0: usize, var: &'static str },
}

/// Which identity (or, in a loop, which identity per iteration) a site folds.
#[derive(Clone, Copy, Debug)]
pub(crate) enum SiteLabel {
    Fixed(FoldLabel),
    /// One identity per iteration `v` of `lp`: `label(v)`.
    Loop {
        lp: FoldLoop,
        label: fn(usize) -> FoldLabel,
    },
}

/// One emitted fold statement.
#[derive(Clone, Debug)]
pub(crate) struct FoldSite {
    /// Yul function containing the statement.
    pub(crate) function: String,
    pub(crate) label: SiteLabel,
    pub(crate) weight: FoldWeight,
    pub(crate) bucket: FoldBucket,
}

impl FoldSite {
    /// The fold statement `bucket += Y_POW[weight] * value`. The direct
    /// emitters write every fold through this function.
    pub(crate) fn statement(&self, value: &str) -> String {
        let bucket = self.bucket.name();
        let weight = match self.weight {
            FoldWeight::Fixed(k) => format!("YP_{k}"),
            FoldWeight::LoopDown { k0, var } => format!("sub(YP_{k0}, shl(5, {var}))"),
        };
        format!("mstore({bucket}, addmod(mload({bucket}), mulmod(mload({weight}), {value}, r), r))")
    }
}

/// Fold sites of one render and the section's call counts.
#[derive(Clone, Debug, Default)]
pub(crate) struct FoldRecord {
    pub(crate) sites: Vec<FoldSite>,
    /// Number of calls of each function by the quotient section.
    pub(crate) calls: BTreeMap<String, usize>,
}

impl FoldRecord {
    /// Record one call of `function` by the section and return its statement.
    pub(crate) fn call(&mut self, function: &str) -> String {
        *self.calls.entry(function.to_string()).or_insert(0) += 1;
        format!("{function}(q_r)")
    }
}

/// Everything the check compares the fold sites against.
#[derive(Clone, Copy, Debug)]
pub(crate) struct FoldContext<'a> {
    pub(crate) manifest: &'a QuotientIdentityManifest,
    /// Number of identities `m` of the program.
    pub(crate) m: usize,
    /// Permutation product sets.
    pub(crate) permutation_sets: usize,
    /// Input chunks per lookup argument (protocol order).
    pub(crate) lookup_chunks: &'a [usize],
    /// Address of `Y_POW[0]` (`YP_k = y_pow + 32 k`).
    pub(crate) y_pow: usize,
    /// Addresses of `Q_BUCKET_s`.
    pub(crate) buckets: &'a [usize],
    /// `SELECTOR_ACC_MPTR`: the PCS reads bucket `s` at `+ 32 s`.
    pub(crate) selector_acc_mptr: usize,
    /// Simple-selector fixed columns in bucket order (the template's
    /// `simple_selector_cols`).
    pub(crate) simple_selector_cols: &'a [usize],
}

/// One expanded fold: identity `j`, weight index `k`, bucket.
#[derive(Clone, Debug)]
struct Fold {
    j: usize,
    k: usize,
    bucket: FoldBucket,
    at: String,
}

fn source_name(source: &QuotientIdentitySource) -> String {
    match source {
        QuotientIdentitySource::Gate {
            gate_index,
            gate_name,
            polynomial_index,
            ..
        } => format!("cs.gates()[{gate_index}] \"{gate_name}\" polynomial[{polynomial_index}]"),
        QuotientIdentitySource::Permutation { identity_index } => {
            format!("permutation identity {identity_index}")
        }
        QuotientIdentitySource::Lookup {
            identity_index,
            lookup_index,
            ..
        } => format!("lookup {lookup_index} identity {identity_index}"),
        QuotientIdentitySource::Trash { trash_index, .. } => format!("trash {trash_index}"),
    }
}

fn target_name(target: QuotientIdentityManifestTarget) -> String {
    match target {
        QuotientIdentityManifestTarget::Main => "Main (Q_MAIN_ACC)".to_string(),
        QuotientIdentityManifestTarget::Selector {
            selector_index,
            fixed_column,
        } => format!(
            "Selector {selector_index} (Q_BUCKET_{selector_index}, fixed column {fixed_column})"
        ),
    }
}

/// `(lookup, index inside the lookup)` of a lookup-family identity, in the
/// order of `logup.rs::expressions`: boundary, one helper per input chunk,
/// accumulator; lookup by lookup.
fn lookup_position(chunks: &[usize], identity_index: usize) -> Option<(usize, usize)> {
    let mut base = 0usize;
    for (lookup, &c) in chunks.iter().enumerate() {
        if identity_index < base + c + 2 {
            return Some((lookup, identity_index - base));
        }
        base += c + 2;
    }
    None
}

/// Manifest entry index of the identity a label names.
fn resolve(label: FoldLabel, ctx: &FoldContext<'_>) -> Result<usize, String> {
    let entries = &ctx.manifest.entries;
    let find = |pred: &dyn Fn(&QuotientIdentitySource) -> bool| {
        entries.iter().position(|e| pred(&e.source))
    };
    let n = ctx.permutation_sets;
    let found = match label {
        FoldLabel::Gate {
            gate_index,
            polynomial_index,
        } => find(&|s| {
            matches!(s, QuotientIdentitySource::Gate { gate_index: g, polynomial_index: p, .. }
                if *g == gate_index && *p == polynomial_index)
        }),
        // permutation.rs::expressions: first-set boundary, last-set boundary,
        // continuity for sets 1..n, product identity for sets 0..n.
        FoldLabel::PermutationFirstBoundary
        | FoldLabel::PermutationLastBoundary
        | FoldLabel::PermutationContinuity { .. }
        | FoldLabel::PermutationProduct { .. } => {
            let local = match label {
                FoldLabel::PermutationFirstBoundary if n > 0 => Some(0),
                FoldLabel::PermutationLastBoundary if n > 0 => Some(1),
                FoldLabel::PermutationContinuity { set } if (1..n).contains(&set) => Some(1 + set),
                FoldLabel::PermutationProduct { set } if set < n => Some(1 + n + set),
                _ => None,
            };
            local.and_then(|local| {
                find(&|s| {
                    matches!(s, QuotientIdentitySource::Permutation { identity_index } if *identity_index == local)
                })
            })
        }
        FoldLabel::LookupBoundary { lookup }
        | FoldLabel::LookupHelper { lookup, .. }
        | FoldLabel::LookupAccumulator { lookup } => {
            let chunks = ctx.lookup_chunks.get(lookup).copied();
            let local = match (label, chunks) {
                (FoldLabel::LookupBoundary { .. }, Some(_)) => Some(0),
                (FoldLabel::LookupHelper { chunk, .. }, Some(c)) if chunk < c => Some(1 + chunk),
                (FoldLabel::LookupAccumulator { .. }, Some(c)) => Some(1 + c),
                _ => None,
            };
            local.and_then(|local| {
                find(&|s| {
                    matches!(s, QuotientIdentitySource::Lookup { identity_index, lookup_index, .. }
                        if *lookup_index == lookup
                            && lookup_position(ctx.lookup_chunks, *identity_index) == Some((lookup, local)))
                })
            })
        }
        FoldLabel::Trash { index } => find(
            &|s| matches!(s, QuotientIdentitySource::Trash { trash_index, .. } if *trash_index == index),
        ),
    };
    found.ok_or_else(|| {
        format!("a fold site folds \"{label}\", which is not an identity of this constraint system")
    })
}

/// Weight index addressed by `YP_k0 - 32 v`.
fn weight_index(ctx: &FoldContext<'_>, k0: usize, v: usize) -> Option<usize> {
    let addr = (ctx.y_pow + k0 * WORD_BYTES).checked_sub(v * WORD_BYTES)?;
    let offset = addr.checked_sub(ctx.y_pow)?;
    (offset % WORD_BYTES == 0 && offset / WORD_BYTES < ctx.m).then_some(offset / WORD_BYTES)
}

/// Prove the fold structure of one render (see the module documentation).
pub(crate) fn check(record: &FoldRecord, ctx: &FoldContext<'_>) -> Result<(), String> {
    let entries = &ctx.manifest.entries;
    if entries.len() != ctx.m {
        return Err(format!(
            "manifest has {} identities, the program folds m = {}",
            entries.len(),
            ctx.m
        ));
    }
    for (i, e) in entries.iter().enumerate() {
        if e.global_index != i {
            return Err(format!(
                "manifest entry {i} has global index {}",
                e.global_index
            ));
        }
    }
    // Bucket words: Q_BUCKET_s must be the word the PCS reads for selector s.
    if ctx.buckets.len() != ctx.simple_selector_cols.len() {
        return Err(format!(
            "{} selector buckets for {} simple-selector columns",
            ctx.buckets.len(),
            ctx.simple_selector_cols.len()
        ));
    }
    for (s, addr) in ctx.buckets.iter().enumerate() {
        if *addr != ctx.selector_acc_mptr + s * WORD_BYTES {
            return Err(format!(
                "Q_BUCKET_{s} is at {addr:#x}, the PCS reads selector {s} at SELECTOR_ACC_MPTR + {:#x}",
                s * WORD_BYTES
            ));
        }
    }

    let mut folds = Vec::new();
    for site in &record.sites {
        let calls = record.calls.get(&site.function).copied().unwrap_or(0);
        let iterations: Vec<(FoldLabel, Option<usize>, String)> = match (site.label, site.weight) {
            (SiteLabel::Fixed(label), FoldWeight::Fixed(k)) => {
                vec![(label, (k < ctx.m).then_some(k), site.function.clone())]
            }
            (SiteLabel::Loop { lp, label }, FoldWeight::LoopDown { k0, var }) => {
                if var != lp.var {
                    return Err(format!(
                        "{}: the weight of the fold in the loop over {} is indexed by {var}",
                        site.function, lp.var
                    ));
                }
                (lp.start..lp.end)
                    .map(|v| {
                        (
                            label(v),
                            weight_index(ctx, k0, v),
                            format!("{} [{} = {v}]", site.function, lp.var),
                        )
                    })
                    .collect()
            }
            (SiteLabel::Fixed(_), FoldWeight::LoopDown { var, .. }) => {
                return Err(format!(
                    "{}: fold outside a loop uses the loop weight of {var}",
                    site.function
                ))
            }
            (SiteLabel::Loop { lp, .. }, FoldWeight::Fixed(k)) => {
                return Err(format!(
                    "{}: every iteration of the loop over {} folds with the same weight Y_POW[{k}]",
                    site.function, lp.var
                ))
            }
        };
        for (label, k, at) in iterations {
            let j = resolve(label, ctx).map_err(|e| format!("{at}: {e}"))?;
            let k = k.ok_or_else(|| {
                format!(
                    "{at}: the fold of identity {j} ({}) addresses a weight outside Y_POW[0..{})",
                    source_name(&entries[j].source),
                    ctx.m
                )
            })?;
            for _ in 0..calls {
                folds.push(Fold {
                    j,
                    k,
                    bucket: site.bucket,
                    at: format!("{at}: {label}"),
                });
            }
        }
    }

    let mut by_j: BTreeMap<usize, Vec<&Fold>> = BTreeMap::new();
    let mut by_k: BTreeMap<usize, Vec<&Fold>> = BTreeMap::new();
    for fold in &folds {
        by_j.entry(fold.j).or_default().push(fold);
        by_k.entry(fold.k).or_default().push(fold);
    }
    let sites_of =
        |folds: &[&Fold]| folds.iter().map(|f| f.at.as_str()).collect::<Vec<_>>().join("; ");
    // 1. No identity is folded twice.
    for (j, folds) in &by_j {
        if folds.len() > 1 {
            return Err(format!(
                "identity {j} ({}) is folded {} times: {}",
                source_name(&entries[*j].source),
                folds.len(),
                sites_of(folds)
            ));
        }
    }
    // 2. No weight is used twice.
    for (k, folds) in &by_k {
        if folds.len() > 1 {
            return Err(format!(
                "weight Y_POW[{k}] is used by {} folds: {}",
                folds.len(),
                sites_of(folds)
            ));
        }
    }
    // 3. Every identity is folded, with its weight, into its bucket.
    for (j, entry) in entries.iter().enumerate() {
        let source = source_name(&entry.source);
        let Some(fold) = by_j.get(&j).and_then(|folds| folds.first()) else {
            return Err(format!(
                "identity {j} ({source}) is not folded by any emitted fold site"
            ));
        };
        let want = ctx.m - 1 - j;
        if fold.k != want {
            return Err(format!(
                "identity {j} ({source}) is folded with Y_POW[{}] at {}; the linearization weight is y^(m-1-j) = Y_POW[{want}]",
                fold.k, fold.at
            ));
        }
        let bucket_ok = match (entry.target, fold.bucket) {
            (QuotientIdentityManifestTarget::Main, FoldBucket::Main) => true,
            (
                QuotientIdentityManifestTarget::Selector {
                    selector_index,
                    fixed_column,
                },
                FoldBucket::Selector(s),
            ) => s == selector_index && ctx.simple_selector_cols.get(s) == Some(&fixed_column),
            _ => false,
        };
        if !bucket_ok {
            return Err(format!(
                "identity {j} ({source}) is folded into {} at {}; its manifest target is {}",
                fold.bucket.name(),
                fold.at,
                target_name(entry.target)
            ));
        }
    }
    // 4. Every weight is used (implied by 1-3; kept as a direct statement).
    if let Some(k) = (0..ctx.m).find(|k| !by_k.contains_key(k)) {
        return Err(format!("weight Y_POW[{k}] is used by no fold"));
    }
    Ok(())
}
