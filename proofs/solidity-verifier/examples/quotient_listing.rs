// SPDX-License-Identifier: CC0-1.0
//! Regenerate and check the quotient-VM listing from deployed VK bytes.
//!
//! An auditor who reviews only the generated contracts can use this tool to
//! confirm that a shipped `QuotientListing` / `QuotientManifest` pair
//! describes a given `Halo2VerifyingKey` (and, optionally, the
//! `Halo2Verifier` that pins it), without running the generator:
//!
//! ```text
//! cargo run --release -p halo2_solidity_verifier --example quotient_listing -- \
//!     <Halo2VerifyingKey.sol | vk-runtime.hex> <QuotientManifest.json> \
//!     [--listing <QuotientListing.txt>] [--verifier <Halo2Verifier.sol>] \
//!     [--evaluator <Halo2QuotientEvaluator.sol>] [--out <blocks.txt>]
//! ```
//!
//! Steps:
//!
//! 1. Read the VK payload, either from the `mstore(add(payload, ...), ...)`
//!    lines of the VK source or from the deployed runtime (`0xfe || payload`)
//!    given as hex, and hash the runtime (= `extcodehash`).
//! 2. Locate the constant table by its keccak256 from the manifest. A VK whose
//!    header is longer or shorter than the manifest's shifts every later
//!    payload word; the shift `delta` (in words) is reported.
//! 3. Extract the program (length from the manifest), hash it, and, when `delta
//!    != 0`, also hash it after moving every memory-pointer operand by
//!    `-32*delta` bytes (the matching shift of the verifier memory layout).
//! 4. Decode the program with the crate's quotient-VM decoder and re-render
//!    every program block using only the VK bytes and the manifest's slot
//!    names, then compare with the manifest (item kinds, byte ranges,
//!    identities, constants used, folds) and, with `--listing`, with the blocks
//!    of the shipped listing, line for line.
//! 5. With `--verifier`, check that the verifier pins this VK runtime
//!    (`EXPECTED_VK_CODEHASH_WORD`, `EXPECTED_VK_LENGTH`) and that the
//!    interpreter (the verifier, or the `--evaluator` contract when the
//!    quotient is delegated to a pinned external evaluator) reads the program
//!    and constants at the expected memory addresses, stops at the expected
//!    length, and uses the manifest's memory anchors (shifted by `32*delta`).
//!
//! Exit status: 0 when every check passes exactly, 2 when every check passes
//! only after the reported payload/memory shift, 1 on any failure.

use std::{collections::BTreeMap, fs, process};

use halo2_solidity_verifier::quotient_listing::{
    extract_program_blocks, relocate_program_pointers, render_program_blocks, ListingSymbols,
    ProgramBlock, ProgramBlockKind, ProgramFold, MANIFEST_FORMAT, MANIFEST_FORMAT_VERSION,
};
use ruint::aliases::U256;
use serde_json::Value;
use sha3::{Digest, Keccak256};

/// Command-line options.
#[derive(Debug, Default)]
pub struct Options {
    /// VK source (`.sol`) or runtime hex file.
    pub vk: String,
    /// Manifest JSON file.
    pub manifest: String,
    /// Optional shipped listing to compare against.
    pub listing: Option<String>,
    /// Optional verifier source to cross-check the VK pins (and, unless an
    /// evaluator is given, the interpreter pointers).
    pub verifier: Option<String>,
    /// Optional `Halo2QuotientEvaluator` source; with an external pinned
    /// quotient evaluator this contract interprets the program.
    pub evaluator: Option<String>,
    /// Optional output file for the regenerated blocks (addresses as in the
    /// given VK).
    pub out: Option<String>,
}

/// Check outcome.
#[derive(Debug, Default)]
pub struct Report {
    /// Human-readable report lines.
    pub lines: Vec<String>,
    /// Number of failed checks.
    pub failures: usize,
    /// Payload shift in words detected between the VK and the manifest.
    pub delta_words: i64,
    /// Regenerated block texts (manifest addresses).
    pub blocks: Vec<String>,
}

impl Report {
    fn pass(&mut self, msg: impl AsRef<str>) {
        self.lines.push(format!("[PASS] {}", msg.as_ref()));
    }
    fn fail(&mut self, msg: impl AsRef<str>) {
        self.failures += 1;
        self.lines.push(format!("[FAIL] {}", msg.as_ref()));
    }
    fn info(&mut self, msg: impl AsRef<str>) {
        self.lines.push(format!("[INFO] {}", msg.as_ref()));
    }
    fn check(&mut self, ok: bool, msg: impl AsRef<str>) {
        if ok {
            self.pass(msg)
        } else {
            self.fail(msg)
        }
    }

    /// Process exit status.
    pub fn status(&self) -> i32 {
        if self.failures > 0 {
            1
        } else if self.delta_words != 0 {
            2
        } else {
            0
        }
    }
}

fn keccak_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Keccak256::digest(bytes).into();
    format!("0x{}", hex::encode(digest))
}

/// `+0x20` / `-0x20` for a signed byte offset.
fn signed_hex(value: i64) -> String {
    if value < 0 {
        format!("-{:#x}", value.unsigned_abs())
    } else {
        format!("+{value:#x}")
    }
}

fn parse_hex_u64(text: &str) -> Option<u64> {
    let text = text.trim();
    let digits = text.strip_prefix("0x").unwrap_or(text);
    u64::from_str_radix(digits, 16).ok()
}

fn parse_num(text: &str) -> Option<u64> {
    let text = text.trim();
    if text.starts_with("0x") {
        parse_hex_u64(text)
    } else {
        text.parse().ok()
    }
}

/// Manifest accessor helpers (all fail with a message naming the field).
fn field<'a>(value: &'a Value, path: &str) -> Result<&'a Value, String> {
    let mut cur = value;
    for key in path.split('.') {
        cur = cur.get(key).ok_or_else(|| format!("manifest is missing `{path}`"))?;
    }
    Ok(cur)
}

fn field_u64(value: &Value, path: &str) -> Result<u64, String> {
    let v = field(value, path)?;
    v.as_u64()
        .or_else(|| v.as_str().and_then(parse_num))
        .ok_or_else(|| format!("manifest field `{path}` is not a number"))
}

fn field_str<'a>(value: &'a Value, path: &str) -> Result<&'a str, String> {
    field(value, path)?
        .as_str()
        .ok_or_else(|| format!("manifest field `{path}` is not a string"))
}

/// VK payload words with optional source labels.
#[derive(Debug, Default)]
pub struct VkPayload {
    /// Payload words (big-endian 32 bytes).
    pub words: Vec<[u8; 32]>,
    /// Source label per word when read from a `.sol` file.
    pub labels: Vec<Option<String>>,
    /// Runtime length declared by the VK source's `return(runtime, len)`.
    pub declared_runtime_len: Option<u64>,
}

impl VkPayload {
    /// Payload bytes.
    pub fn bytes(&self) -> Vec<u8> {
        self.words.iter().flatten().copied().collect()
    }

    /// Runtime bytes (`0xfe || payload`).
    pub fn runtime(&self) -> Vec<u8> {
        let mut out = vec![0xfe];
        out.extend(self.bytes());
        out
    }
}

/// Parse a generated `Halo2VerifyingKey*.sol` source.
pub fn parse_vk_source(source: &str) -> Result<VkPayload, String> {
    let mut entries = Vec::new();
    let mut declared = None;
    for line in source.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("mstore(add(payload, ") {
            let (offset, rest) =
                rest.split_once("), ").ok_or_else(|| format!("unparsed VK line: {line}"))?;
            let (word, rest) =
                rest.split_once(')').ok_or_else(|| format!("unparsed VK line: {line}"))?;
            let offset = parse_hex_u64(offset).ok_or_else(|| format!("bad offset in: {line}"))?;
            let digits = word.trim().trim_start_matches("0x");
            if digits.len() != 64 {
                return Err(format!("VK word is not 32 bytes: {line}"));
            }
            let mut bytes = [0u8; 32];
            hex::decode_to_slice(digits, &mut bytes).map_err(|e| format!("{e}: {line}"))?;
            let label = rest.trim().strip_prefix("//").map(|l| l.trim().to_string());
            entries.push((offset, bytes, label));
        } else if let Some(rest) = line.strip_prefix("return(runtime, ") {
            declared = rest
                .trim_end_matches(')')
                .trim()
                .parse::<u64>()
                .ok()
                .or_else(|| parse_hex_u64(rest.trim_end_matches(')')));
        }
    }
    if entries.is_empty() {
        return Err("no `mstore(add(payload, ...), ...)` lines found in the VK source".to_string());
    }
    let mut payload = VkPayload {
        declared_runtime_len: declared,
        ..VkPayload::default()
    };
    for (idx, (offset, word, label)) in entries.into_iter().enumerate() {
        if offset != 32 * idx as u64 {
            return Err(format!(
                "VK source payload words are not contiguous: word {idx} is stored at {offset:#x}"
            ));
        }
        payload.words.push(word);
        payload.labels.push(label);
    }
    Ok(payload)
}

/// Parse a deployed runtime given as hex (`0xfe || payload`).
pub fn parse_vk_runtime_hex(text: &str) -> Result<VkPayload, String> {
    let digits: String = text
        .trim()
        .trim_start_matches("0x")
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect();
    let bytes = hex::decode(&digits).map_err(|e| format!("runtime hex: {e}"))?;
    let (first, rest) = bytes.split_first().ok_or("empty runtime")?;
    if *first != 0xfe {
        return Err(format!(
            "runtime byte 0 is {first:#04x}, expected the 0xfe INVALID prefix"
        ));
    }
    if rest.len() % 32 != 0 {
        return Err(format!(
            "runtime payload length {} is not a multiple of 32",
            rest.len()
        ));
    }
    Ok(VkPayload {
        words: rest.chunks(32).map(|c| c.try_into().expect("32 bytes")).collect(),
        labels: vec![None; rest.len() / 32],
        declared_runtime_len: None,
    })
}

/// Integer constants declared in a verifier source.
fn parse_verifier(source: &str) -> BTreeMap<String, u64> {
    let mut out = BTreeMap::new();
    for line in source.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("uint256 internal constant") {
            if let Some((name, value)) = rest.split_once('=') {
                let value = value.trim().trim_end_matches(';').trim();
                let value = value.split_whitespace().next().unwrap_or("");
                if let Some(v) = parse_num(value) {
                    out.insert(name.trim().to_string(), v);
                }
            }
        }
        for key in ["q_const_mptr", "q_program_mptr"] {
            if let Some(rest) = line.strip_prefix(&format!("let {key} := ")) {
                if let Some(v) = parse_num(rest) {
                    out.insert(key.to_string(), v);
                }
            }
        }
        if let Some(rest) = line.strip_prefix("let q_end := add(q_program_mptr, ") {
            if let Some(v) = parse_num(rest.trim_end_matches(')')) {
                out.insert("q_len".to_string(), v);
            }
        }
    }
    out
}

/// `EXPECTED_VK_CODEHASH_WORD` from a verifier source.
fn parse_verifier_codehash(source: &str) -> Option<String> {
    source.lines().find_map(|line| {
        let rest = line
            .trim()
            .strip_prefix("uint256 internal constant EXPECTED_VK_CODEHASH_WORD =")?;
        Some(rest.trim().trim_end_matches(';').trim().to_ascii_lowercase())
    })
}

/// Build the listing symbols from the manifest, optionally shifting every
/// address `>= min_addr` by `delta` bytes.
fn manifest_symbols(manifest: &Value, min_addr: u64, delta: i64) -> Result<ListingSymbols, String> {
    let shift = |addr: u64| -> u32 {
        if addr >= min_addr {
            (addr as i64 + delta) as u32
        } else {
            addr as u32
        }
    };
    let mut symbols = ListingSymbols::default();
    for slot in field(manifest, "slots")?.as_array().ok_or("`slots` is not an array")? {
        let addr = field_u64(slot, "memory")?;
        symbols.slots.insert(shift(addr), field_str(slot, "name")?.to_string());
    }
    for token in field(manifest, "tokens")?.as_array().ok_or("`tokens` is not an array")? {
        symbols.tokens.insert(
            field_u64(token, "token")? as u8,
            (
                field_str(token, "symbol")?.to_string(),
                shift(field_u64(token, "memory")?),
            ),
        );
    }
    Ok(symbols)
}

/// Run all checks.
pub fn check(opts: &Options) -> Result<Report, String> {
    let mut report = Report::default();
    let manifest_text =
        fs::read_to_string(&opts.manifest).map_err(|e| format!("{}: {e}", opts.manifest))?;
    let manifest: Value =
        serde_json::from_str(&manifest_text).map_err(|e| format!("{}: {e}", opts.manifest))?;
    let format = field_str(&manifest, "format")?;
    let version = field_u64(&manifest, "format_version")?;
    if format != MANIFEST_FORMAT || version != MANIFEST_FORMAT_VERSION as u64 {
        return Err(format!(
            "unsupported manifest format {format} v{version} (this tool reads {MANIFEST_FORMAT} v{MANIFEST_FORMAT_VERSION})"
        ));
    }
    report.info(format!(
        "manifest {}: generator {} {}, m = {} identities",
        opts.manifest,
        field_str(&manifest, "generator.crate")?,
        field_str(&manifest, "generator.version")?,
        field_u64(&manifest, "identities.m")?
    ));

    // 1. VK payload.
    let vk_text = fs::read_to_string(&opts.vk).map_err(|e| format!("{}: {e}", opts.vk))?;
    let vk = if vk_text.contains("mstore(add(payload,") {
        parse_vk_source(&vk_text)?
    } else {
        parse_vk_runtime_hex(&vk_text)?
    };
    let payload = vk.bytes();
    let runtime = vk.runtime();
    let codehash = keccak_hex(&runtime);
    report.info(format!(
        "VK {}: {} payload words, runtime {} bytes, keccak256(runtime) = {codehash}",
        opts.vk,
        vk.words.len(),
        runtime.len()
    ));
    if let Some(declared) = vk.declared_runtime_len {
        report.check(
            declared == runtime.len() as u64,
            format!(
                "VK source returns {declared} runtime bytes = 1 + 32 * {} words",
                vk.words.len()
            ),
        );
    }
    let manifest_codehash = field_str(&manifest, "vk.runtime_codehash")?;
    let exact_vk = codehash == manifest_codehash;
    if exact_vk {
        report.pass(format!(
            "VK runtime codehash equals the manifest ({manifest_codehash})"
        ));
    } else {
        report.info(format!(
            "VK runtime codehash differs from the manifest ({manifest_codehash}); checking the quotient sections"
        ));
    }

    // 2. Constant table, located by hash.
    let const_off = field_u64(&manifest, "constants.vk_payload_word_offset")? as i64;
    let const_count = field_u64(&manifest, "constants.count")? as usize;
    let const_hash = field_str(&manifest, "constants.keccak256")?;
    let words_hash = |start: i64, count: usize| -> Option<String> {
        if start < 0 || start as usize + count > vk.words.len() {
            return None;
        }
        let bytes: Vec<u8> = vk.words[start as usize..start as usize + count]
            .iter()
            .flatten()
            .copied()
            .collect();
        Some(keccak_hex(&bytes))
    };
    let delta = [0i64]
        .into_iter()
        .chain((1..=16).flat_map(|d| [d, -d]))
        .find(|d| words_hash(const_off + d, const_count).as_deref() == Some(const_hash));
    let Some(delta) = delta else {
        report.fail(format!(
            "constant table ({const_count} words, keccak256 {const_hash}) not found near payload word {const_off}"
        ));
        return Ok(report);
    };
    report.delta_words = delta;
    let const_start = (const_off + delta) as usize;
    report.pass(format!(
        "constant table: {const_count} words at payload words [{const_start}, {}) hash to the manifest's {const_hash}",
        const_start + const_count
    ));
    if delta != 0 {
        report.info(format!(
            "payload shift: the quotient sections start {delta:+} word(s) from the manifest's offsets (manifest word {const_off}, VK word {const_start})"
        ));
    }
    if let Some(label) = vk.labels.get(const_start).cloned().flatten() {
        let labels_ok = vk.labels[const_start..const_start + const_count]
            .iter()
            .all(|l| l.as_deref() == Some("quotient_const"));
        report.check(
            labels_ok,
            format!("VK source labels the constant words `quotient_const` (first label: {label})"),
        );
    }
    let consts = vk.words[const_start..const_start + const_count]
        .iter()
        .map(|w| U256::from_be_bytes(*w))
        .collect::<Vec<_>>();

    // 3. Program bytes.
    let prog_off = field_u64(&manifest, "program.vk_payload_word_offset")? as i64 + delta;
    let prog_words = field_u64(&manifest, "program.vk_payload_word_count")? as usize;
    let prog_len = field_u64(&manifest, "program.length_bytes")? as usize;
    let prog_hash = field_str(&manifest, "program.keccak256")?;
    let prog_start = prog_off as usize * 32;
    if prog_off < 0 || prog_start + prog_words * 32 > payload.len() || prog_len > prog_words * 32 {
        report.fail("program section is outside the VK payload");
        return Ok(report);
    }
    let raw_program = payload[prog_start..prog_start + prog_len].to_vec();
    let padding_zero = payload[prog_start + prog_len..prog_start + prog_words * 32]
        .iter()
        .all(|b| *b == 0);
    report.check(
        padding_zero,
        format!(
            "program: {prog_len} bytes at payload bytes [{prog_start:#06x}, {:#06x}), {} padding bytes zero",
            prog_start + prog_len,
            prog_words * 32 - prog_len
        ),
    );
    if let Some(label) = vk.labels.get(prog_off as usize).cloned().flatten() {
        let labels_ok = vk.labels[prog_off as usize..prog_off as usize + prog_words]
            .iter()
            .all(|l| l.as_deref() == Some("quotient_program"));
        report.check(
            labels_ok,
            format!("VK source labels the program words `quotient_program` (first label: {label})"),
        );
    }
    let vk_mptr = field_u64(&manifest, "vk.vk_mptr")?;
    let raw_hash = keccak_hex(&raw_program);
    let program = if raw_hash == prog_hash {
        report.pass(format!(
            "program keccak256 equals the manifest ({prog_hash})"
        ));
        raw_program.clone()
    } else if delta != 0 {
        match relocate_program_pointers(&raw_program, vk_mptr as u32, -32 * delta) {
            Ok((moved, count)) => {
                let moved_hash = keccak_hex(&moved);
                report.info(format!(
                    "raw program keccak256 {raw_hash} differs from the manifest"
                ));
                report.check(
                    moved_hash == prog_hash,
                    format!(
                        "program keccak256 equals the manifest after moving all {count} memory-pointer operands >= {vk_mptr:#x} by {} bytes (opcodes, constant slots, counts, folds unchanged)",
                        signed_hex(-32 * delta)
                    ),
                );
                moved
            }
            Err(err) => {
                report.fail(format!("program does not decode for relocation: {err}"));
                return Ok(report);
            }
        }
    } else {
        report.fail(format!(
            "program keccak256 {raw_hash} differs from the manifest's {prog_hash}"
        ));
        raw_program.clone()
    };

    // 4. Regenerate program blocks from the bytes and manifest names.
    let symbols = manifest_symbols(&manifest, 0, 0)?;
    let items = field(&manifest, "program_items")?
        .as_array()
        .ok_or("`program_items` is not an array")?;
    let item_identities = items
        .iter()
        .map(|item| {
            field(item, "identities")?
                .as_array()
                .ok_or_else(|| "`identities` is not an array".to_string())?
                .iter()
                .map(|j| j.as_u64().map(|j| j as usize).ok_or_else(|| "bad j".to_string()))
                .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    let program_mptr = field_u64(&manifest, "program.memory_start")? as u32;
    let blocks =
        match render_program_blocks(&program, &consts, program_mptr, &symbols, &item_identities) {
            Ok(blocks) => blocks,
            Err(err) => {
                report.fail(format!(
                    "program does not decode into the manifest's items: {err}"
                ));
                return Ok(report);
            }
        };
    report.pass(format!(
        "decoded {} program items; listing lines cover every program byte exactly once",
        blocks.len()
    ));
    let mut item_errors = Vec::new();
    for (idx, (block, item)) in blocks.iter().zip(items).enumerate() {
        let kind = field_str(item, "kind")?;
        let start = field_u64(item, "byte_start")? as usize;
        let end = field_u64(item, "byte_end")? as usize;
        if kind != block.kind.label() || start != block.byte_start || end != block.byte_end {
            item_errors.push(format!(
                "item {idx}: bytes decode as {} [{:#06x}, {:#06x}), manifest says {kind} [{start:#06x}, {end:#06x})",
                block.kind.label(),
                block.byte_start,
                block.byte_end
            ));
        }
        if let ProgramBlockKind::NativeIdentity { index } = block.kind {
            if field_u64(item, "native_index").ok() != Some(u64::from(index)) {
                item_errors.push(format!(
                    "item {idx}: native index {index} differs from the manifest"
                ));
            }
        }
    }
    report.check(
        item_errors.is_empty(),
        format!(
            "program items match the manifest (kinds, byte ranges, identities){}",
            item_errors.first().map(|e| format!(": {e}")).unwrap_or_default()
        ),
    );
    let entry_errors = check_entries(&manifest, &blocks)?;
    report.check(
        entry_errors.is_empty(),
        format!(
            "manifest entries agree with the bytes (execution kind, byte range, constants used, fold bucket and gap){}",
            entry_errors.first().map(|e| format!(": {e}")).unwrap_or_default()
        ),
    );
    report.blocks = blocks.iter().map(|b| b.text.clone()).collect();

    // 5. Shipped listing.
    if let Some(path) = &opts.listing {
        let listing = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        let listing_hash = keccak_hex(listing.as_bytes());
        report.check(
            listing_hash == field_str(&manifest, "listing.keccak256")?,
            format!("listing file keccak256 {listing_hash} matches the manifest"),
        );
        let shipped = extract_program_blocks(&listing);
        let first_diff = shipped.iter().zip(&report.blocks).position(|(a, b)| a != b);
        let ok = shipped.len() == report.blocks.len() && first_diff.is_none();
        let detail = match first_diff {
            Some(idx) => {
                let (a, b) = (&shipped[idx], &report.blocks[idx]);
                let line = a
                    .lines()
                    .zip(b.lines())
                    .find(|(x, y)| x != y)
                    .map(|(x, y)| format!("\n         shipped:     {x}\n         regenerated: {y}"))
                    .unwrap_or_default();
                format!(": first difference in block {idx}{line}")
            }
            None if shipped.len() != report.blocks.len() => format!(
                ": listing has {} blocks, bytes decode to {}",
                shipped.len(),
                report.blocks.len()
            ),
            None => String::new(),
        };
        report.check(
            ok,
            format!(
                "{} regenerated program blocks are identical to the shipped listing{detail}",
                report.blocks.len()
            ),
        );
    }

    // 6. Verifier / evaluator cross-checks.
    if let Some(path) = &opts.verifier {
        let source = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        let consts_v = parse_verifier(&source);
        match parse_verifier_codehash(&source) {
            Some(pinned) => report.check(
                pinned == codehash,
                format!("verifier pins EXPECTED_VK_CODEHASH_WORD = {pinned} = keccak256 of this VK runtime"),
            ),
            None => report.info("verifier source has no EXPECTED_VK_CODEHASH_WORD (embedded VK?)"),
        }
        if let Some(len) = consts_v.get("EXPECTED_VK_LENGTH") {
            report.check(
                *len == runtime.len() as u64,
                format!("verifier pins EXPECTED_VK_LENGTH = {len} = this VK runtime length"),
            );
        }
    }
    let interpreter = opts
        .evaluator
        .as_ref()
        .map(|p| ("evaluator", p))
        .or(opts.verifier.as_ref().map(|p| ("verifier", p)));
    if let Some((who, path)) = interpreter {
        let source = fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?;
        let consts_v = parse_verifier(&source);
        if !consts_v.contains_key("q_program_mptr") {
            report.info(format!(
                "{who} does not interpret the program (external quotient evaluator?); pass it with --evaluator to check the interpreter pointers"
            ));
        } else {
            let shift = 32 * delta;
            let vk_mptr_v = consts_v.get("VK_MPTR").copied();
            report.check(
                vk_mptr_v == Some(vk_mptr),
                format!(
                    "{who} VK_MPTR = {:#x} (manifest {vk_mptr:#x})",
                    vk_mptr_v.unwrap_or(0)
                ),
            );
            let q_const = consts_v.get("q_const_mptr").copied();
            let want_const = vk_mptr + 32 * const_start as u64;
            report.check(
                q_const == Some(want_const),
                format!(
                    "{who} q_const_mptr = {:#x} = VK_MPTR + 32 * {const_start}",
                    q_const.unwrap_or(0)
                ),
            );
            let q_prog = consts_v.get("q_program_mptr").copied();
            let want_prog = vk_mptr + 32 * prog_off as u64;
            report.check(
                q_prog == Some(want_prog),
                format!(
                    "{who} q_program_mptr = {:#x} = VK_MPTR + 32 * {prog_off}",
                    q_prog.unwrap_or(0)
                ),
            );
            let q_len = consts_v.get("q_len").copied();
            report.check(
                q_len == Some(prog_len as u64),
                format!(
                    "{who} interprets q_end = q_program_mptr + {:#x} (program length {prog_len:#x})",
                    q_len.unwrap_or(0)
                ),
            );
            let mut anchors = vec![
                (
                    "REVERSED_EVALS_MPTR".to_string(),
                    field_u64(&manifest, "memory.REVERSED_EVALS_MPTR")?,
                ),
                (
                    "CHALLENGE_MPTR".to_string(),
                    field_u64(&manifest, "memory.CHALLENGE_MPTR")?,
                ),
                (
                    "SELECTOR_ACC_MPTR".to_string(),
                    field_u64(&manifest, "memory.SELECTOR_ACC_MPTR")?,
                ),
            ];
            for token in field(&manifest, "tokens")?.as_array().ok_or("tokens")? {
                anchors.push((
                    field_str(token, "symbol")?.to_string(),
                    field_u64(token, "memory")?,
                ));
            }
            let mut anchor_errors = Vec::new();
            for (name, manifest_addr) in &anchors {
                let want = (*manifest_addr as i64 + shift) as u64;
                match consts_v.get(name) {
                    Some(actual) if *actual == want => {}
                    Some(actual) => {
                        anchor_errors.push(format!("{name} = {actual:#x}, expected {want:#x}"))
                    }
                    None => anchor_errors.push(format!("{name} not declared")),
                }
            }
            report.check(
                anchor_errors.is_empty(),
                format!(
                    "{who} memory anchors ({} names: REVERSED_EVALS_MPTR, CHALLENGE_MPTR, SELECTOR_ACC_MPTR, VM tokens) equal the manifest{}{}",
                    anchors.len(),
                    if shift != 0 { format!(" shifted by {}", signed_hex(shift)) } else { String::new() },
                    anchor_errors.first().map(|e| format!(": {e}")).unwrap_or_default()
                ),
            );
        }
    }

    // 7. Regenerated blocks in the given VK's own addresses.
    if let Some(path) = &opts.out {
        let text = if delta == 0 {
            report.blocks.join("\n")
        } else {
            let shifted = manifest_symbols(&manifest, vk_mptr, 32 * delta)?;
            render_program_blocks(
                &raw_program,
                &consts,
                (program_mptr as i64 + 32 * delta) as u32,
                &shifted,
                &item_identities,
            )?
            .iter()
            .map(|b| b.text.clone())
            .collect::<Vec<_>>()
            .join("\n")
        };
        fs::write(path, format!("{text}\n")).map_err(|e| format!("{path}: {e}"))?;
        report.info(format!(
            "wrote regenerated program blocks for this VK's addresses to {path}"
        ));
    }
    Ok(report)
}

/// Compare per-identity manifest entries with the decoded blocks.
fn check_entries(manifest: &Value, blocks: &[ProgramBlock]) -> Result<Vec<String>, String> {
    let mut errors = Vec::new();
    let entries = field(manifest, "entries")?.as_array().ok_or("`entries` is not an array")?;
    let m = field_u64(manifest, "identities.m")? as usize;
    if entries.len() != m {
        errors.push(format!("{} entries for m = {m}", entries.len()));
    }
    let mut seen = vec![false; m];
    for (pos, entry) in entries.iter().enumerate() {
        let j = field_u64(entry, "j")? as usize;
        if j != pos || j >= m || seen[j] {
            errors.push(format!("entry {pos} has j = {j}"));
            continue;
        }
        seen[j] = true;
        if field_u64(entry, "y_exponent")? as usize != m - 1 - j {
            errors.push(format!("j={j}: y_exponent is not m-1-j"));
        }
        let execution = field(entry, "execution")?;
        let kind = field_str(execution, "kind")?;
        let Ok(item) = field_u64(execution, "program_item") else {
            if matches!(
                kind,
                "vm_bytecode" | "native_gate_callback" | "native_permutation" | "native_lookup"
            ) {
                errors.push(format!("j={j}: {kind} without a program item"));
            }
            continue;
        };
        let Some(block) = blocks.get(item as usize) else {
            errors.push(format!("j={j}: program item {item} does not exist"));
            continue;
        };
        if kind != block.kind.label() || !block.identities.contains(&j) {
            errors.push(format!(
                "j={j}: bytes of item {item} are {} for {:?}",
                block.kind.label(),
                block.identities
            ));
        }
        if field_u64(execution, "byte_start")? as usize != block.byte_start
            || field_u64(execution, "byte_end")? as usize != block.byte_end
        {
            errors.push(format!("j={j}: byte range differs from the decoded item"));
        }
        if kind == "vm_bytecode" {
            let used = field(execution, "constants_used")?
                .as_array()
                .ok_or("constants_used")?
                .iter()
                .filter_map(|c| c.as_u64().map(|c| c as u16))
                .collect::<Vec<_>>();
            if used != block.constants_used {
                errors.push(format!("j={j}: constants_used differs from the bytes"));
            }
            let target = field(entry, "target")?;
            let fold_ok = match (field_str(target, "bucket")?, block.fold) {
                ("main", Some(ProgramFold::Main)) => true,
                ("selector", Some(ProgramFold::Selector { selector, gap })) => {
                    field_u64(target, "selector_index")? == u64::from(selector)
                        && field_u64(target, "gap")? == u64::from(gap)
                }
                _ => false,
            };
            if !fold_ok {
                errors.push(format!(
                    "j={j}: fold {:?} does not match the target bucket",
                    block.fold
                ));
            }
        }
    }
    Ok(errors)
}

/// Parse command-line arguments.
pub fn parse_args(args: &[String]) -> Result<Options, String> {
    let mut opts = Options::default();
    let mut positional = Vec::new();
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        let mut value =
            |name: &str| iter.next().cloned().ok_or_else(|| format!("{name} needs a value"));
        match arg.as_str() {
            "--listing" => opts.listing = Some(value("--listing")?),
            "--verifier" => opts.verifier = Some(value("--verifier")?),
            "--evaluator" => opts.evaluator = Some(value("--evaluator")?),
            "--out" => opts.out = Some(value("--out")?),
            "-h" | "--help" => return Err(usage()),
            other => positional.push(other.to_string()),
        }
    }
    match positional.as_slice() {
        [vk, manifest] => {
            opts.vk = vk.clone();
            opts.manifest = manifest.clone();
            Ok(opts)
        }
        _ => Err(usage()),
    }
}

fn usage() -> String {
    "usage: quotient_listing <Halo2VerifyingKey.sol | vk-runtime.hex> <QuotientManifest.json> \
     [--listing <QuotientListing.txt>] [--verifier <Halo2Verifier.sol>] \
     [--evaluator <Halo2QuotientEvaluator.sol>] [--out <blocks.txt>]"
        .to_string()
}

/// Entry point shared with the integration tests.
pub fn run(args: &[String]) -> i32 {
    let opts = match parse_args(args) {
        Ok(opts) => opts,
        Err(err) => {
            eprintln!("{err}");
            return 1;
        }
    };
    match check(&opts) {
        Ok(report) => {
            for line in &report.lines {
                println!("{line}");
            }
            let status = report.status();
            println!(
                "result: {}",
                match status {
                    0 => "all checks passed".to_string(),
                    2 => format!(
                        "all checks passed after the reported {:+}-word payload shift",
                        report.delta_words
                    ),
                    _ => format!("{} check(s) failed", report.failures),
                }
            );
            status
        }
        Err(err) => {
            eprintln!("error: {err}");
            1
        }
    }
}

#[allow(dead_code)]
fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    process::exit(run(&args));
}
