// SPDX-License-Identifier: CC0-1.0
//! P14 (L-1, docs/audit/HALO2_VERIFIER_REVIEW_2026-08.md): the committed
//! replay fixtures compile PRE-RENDERED `.sol` sources, so a template edit
//! whose fixtures were not regenerated keeps every replay test green while
//! the deployable artifacts silently drift. This test pins a digest of the
//! whole `templates/` tree; editing any template forces an explicit
//! regeneration acknowledgement. Deliberately not feature-gated so it runs
//! in default CI with no SRS, no solc, and no EVM.

use std::{fs, path::Path};

use sha3::{Digest, Keccak256};

/// keccak over the sorted (path, length, content) stream of `templates/`.
const EXPECTED_TEMPLATE_TREE_DIGEST: &str =
    "0xfe89267c0778787678b938eb6f56f5e79f4bc11578786da45f2aad82384349d9";

fn collect_files(dir: &Path, files: &mut Vec<std::path::PathBuf>) {
    for entry in fs::read_dir(dir).expect("template directory is readable") {
        let path = entry.expect("template directory entry is readable").path();
        if path.is_dir() {
            collect_files(&path, files);
        } else {
            files.push(path);
        }
    }
}

#[test]
fn template_tree_digest_is_pinned() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("templates");
    let mut files = Vec::new();
    collect_files(&root, &mut files);
    files.sort();
    assert!(
        files.len() >= 15,
        "template tree unexpectedly small ({} files); digest coverage would be vacuous",
        files.len()
    );

    let mut hasher = Keccak256::new();
    for path in &files {
        let rel = path
            .strip_prefix(&root)
            .expect("collected paths live under templates/")
            .to_string_lossy()
            .replace('\\', "/");
        let content = fs::read(path).expect("template file is readable");
        hasher.update((rel.len() as u64).to_be_bytes());
        hasher.update(rel.as_bytes());
        hasher.update((content.len() as u64).to_be_bytes());
        hasher.update(&content);
    }
    let actual = format!("0x{}", hex::encode(hasher.finalize()));

    assert_eq!(
        actual, EXPECTED_TEMPLATE_TREE_DIGEST,
        "\n\nThe templates/ tree changed (digest {actual}). Every committed \
         fixture and dump was rendered from the previous tree and is now \
         stale. Before updating EXPECTED_TEMPLATE_TREE_DIGEST in this test:\n\
         \x20 1. regenerate the fixture dumps (fixture tests + \
         scripts/run_ivc_bench.sh) and the committed fixtures/ where \
         applicable (see each fixtures/*/README.md);\n\
         \x20 2. update the source-commit stamps in those READMEs;\n\
         \x20 3. re-run the replay tests against the regenerated artifacts;\n\
         then pin the new digest.\n"
    );
}
