//! Shared fixture-test helpers.

use std::{fs, path::PathBuf};

use halo2_solidity_verifier::RenderedArtifacts;

#[path = "../../examples/quotient_listing.rs"]
#[allow(dead_code)]
mod tool;

/// Check the quotient listing and manifest of a separate-VK fixture render:
/// both are present, the render-time validation recorded full byte and
/// identity coverage, and the `quotient_listing` auditor example regenerates
/// every program block from the VK source and agrees with the listing,
/// the manifest hashes and the verifier's pins.
///
/// The artifacts are written under `CARGO_TARGET_TMPDIR`, never into the
/// tracked fixture dump directories.
#[allow(dead_code)]
pub fn check_quotient_listing(name: &str, artifacts: &RenderedArtifacts) {
    let listing = artifacts.quotient_listing.as_ref().expect("quotient listing emitted");
    let manifest_text = artifacts.quotient_manifest.as_ref().expect("quotient manifest emitted");
    let vk = artifacts.verifying_key.as_ref().expect("separate VK render");
    let manifest: serde_json::Value = serde_json::from_str(manifest_text).expect("manifest JSON");

    let validation = &manifest["validation"];
    assert_eq!(validation["program_bytes_covered_once"], true);
    assert_eq!(validation["identities_executed_once_in_order"], true);
    assert_eq!(validation["numeric_agree"], validation["vm_identities"]);
    let m = manifest["identities"]["m"].as_u64().unwrap() as usize;
    let entries = manifest["entries"].as_array().unwrap();
    assert_eq!(entries.len(), m);
    for (j, entry) in entries.iter().enumerate() {
        assert_eq!(
            entry["j"].as_u64(),
            Some(j as u64),
            "{name}: manifest entry order"
        );
        assert_eq!(entry["y_exponent"].as_u64(), Some((m - 1 - j) as u64));
    }

    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("{name}-quotient-listing"));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("Halo2Verifier.sol"), &artifacts.verifier).unwrap();
    fs::write(dir.join("Halo2VerifyingKey.sol"), vk).unwrap();
    fs::write(dir.join("QuotientListing.txt"), listing).unwrap();
    fs::write(dir.join("QuotientManifest.json"), manifest_text).unwrap();
    if let Some(evaluator) = &artifacts.quotient_evaluator {
        fs::write(dir.join("Halo2QuotientEvaluator.sol"), evaluator).unwrap();
    }
    let report = tool::check(&tool::Options {
        vk: dir.join("Halo2VerifyingKey.sol").display().to_string(),
        manifest: dir.join("QuotientManifest.json").display().to_string(),
        listing: Some(dir.join("QuotientListing.txt").display().to_string()),
        verifier: Some(dir.join("Halo2Verifier.sol").display().to_string()),
        evaluator: artifacts
            .quotient_evaluator
            .as_ref()
            .map(|_| dir.join("Halo2QuotientEvaluator.sol").display().to_string()),
        out: None,
    })
    .expect("quotient_listing tool runs");
    assert_eq!(
        report.failures,
        0,
        "{name}: quotient_listing tool failures:\n{}",
        report.lines.join("\n")
    );
    assert_eq!(report.status(), 0, "{name}: exact round trip expected");
    eprintln!(
        "[{name}] quotient listing: m={m}, VM identities={} (numeric agree {}, symbolic equal {}), program {} bytes in {} items, listing {} lines; tool round trip ok ({} checks)",
        validation["vm_identities"],
        validation["numeric_agree"],
        validation["symbolic_equal"],
        manifest["program"]["length_bytes"],
        manifest["program_items"].as_array().unwrap().len(),
        listing.lines().count(),
        report.lines.iter().filter(|l| l.starts_with("[PASS]")).count()
    );
}
