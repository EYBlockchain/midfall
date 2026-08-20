#![no_main]

//! Raw-byte fuzzing of the compact quotient VM's checked decode/validation
//! gates and the reference interpreter (assurance gap G6).
//!
//! The property is totality: `validate_quotient_program`,
//! `validate_quotient_const_slots`, `validate_quotient_reencode`, and the
//! reference evaluation of every accepted identity segment must never panic,
//! no matter the input bytes. The proptest suite in
//! `src/lowering/quotient_numerator/vm/proptests.rs` covers the same
//! properties with structured generators; this target explores the raw byte
//! space.

use halo2_solidity_verifier::__fuzz_only_quotient_vm_decode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|bytes: &[u8]| {
    __fuzz_only_quotient_vm_decode(bytes);
});
