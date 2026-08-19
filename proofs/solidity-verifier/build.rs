// SPDX-License-Identifier: CC0-1.0
//! Exposes the crate's enabled feature profile to the generator (P10/L-8,
//! docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md).
//!
//! The rendered verifier's proof schema depends on feature flags
//! (`truncated-challenges`, `fewer-point-sets`, ...), and nothing in the
//! deployed artifact previously recorded which profile produced it. The
//! generator folds this string into the emitted `BUILD_ID` constant.

fn main() {
    let mut features: Vec<String> = std::env::vars()
        .filter_map(|(key, _)| {
            key.strip_prefix("CARGO_FEATURE_")
                .map(|name| name.to_ascii_lowercase().replace('_', "-"))
        })
        .collect();
    features.sort();
    println!(
        "cargo:rustc-env=SOLIDITY_VERIFIER_FEATURES={}",
        features.join(",")
    );
    println!("cargo:rerun-if-changed=build.rs");
}
