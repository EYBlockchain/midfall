-- |
-- Midfall.Yul.ImportSolcIR
--
-- GENERATED FILE - do not edit by hand. Everything below the GENERATED-BODY-BELOW marker is
-- produced by formal/scripts/gen_import_solc_ir.py from the pinned solc "ir" artifact of the
-- tracked deployed sources. Regenerate with
--
--     cd formal && python3 scripts/gen_import_solc_ir.py
--     python3 scripts/gen_import_solc_ir.py --check    # fails if this file is stale
--
-- D-P15 (docs/design.md): the via-IR import is TEXTUAL - solc's own IR, quoted as yulObject%
-- terms, with the elaborator as the checker. This module is that import, and it is what makes
-- Midfall.Lowering.RunContractIR inhabited: until now no imported object existed anywhere in
-- the tree, so every theorem whose only hypothesis was a RunContractIR was vacuously true, and
-- that is exactly why stage 4 declined to state lowering_equivalence.
--
-- ## Provenance (pinned here, re-derived by the gates at the bottom of this file)
--
--   compiler    Version: 0.8.30+commit.73712a01.Darwin.appleclang
--   solc sha256 738dcdc6afddeb505ee4e4ef24f1c1fdba2b8c924e614cbbf5801a5b062dd683
--   solc path   proofs/solidity-verifier/.solc/solc
--   settings    viaIR=true, optimizer.enabled=true, optimizer.runs=200, evmVersion=cancun, metadata.bytecodeHash=none
--   output      ir - the PRE-optimisation textual via-IR
--
-- The standard-json payload is built in one place, scripts/gen_import_solc_ir.py, and that
-- script refuses to run against a compiler whose digest is not the one above. The artifact
-- text is committed verbatim beside this file:
--
-- * `Midfall/Yul/solc-ir-Halo2Verifier.yul` - the ir of `proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol`: 2898 lines, 192150 bytes, 4580 dollar signs, sha256 `a3e3923ecca9b4ebaaf2e357446d4a745b75fb2763c7a4a4c4f2e745aac1d109`
-- * `Midfall/Yul/solc-ir-Halo2VerifyingKey.yul` - the ir of `proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.sol`: 604 lines, 64329 bytes, 537 dollar signs, sha256 `af3ccbdbf57bae598ef99dc383b5684ae70bc632db4ab39c241c349eae6724bf`
--
-- so the import is reproducible from the tracked sources and auditable against the bytes solc
-- emitted, rather than being a paste of something nobody can regenerate (hazard 1 of
-- docs/plans/P-IR-import.md).
--
-- ## DECISION 1: ir is pinned, not irOptimized - the memoryguard divergence is a stated
-- ## consequence of the trusted hop, not a defect
--
-- memoryguard survives BOTH artifacts, with a different ARGUMENT:
--
-- * `Halo2Verifier`: ir says memoryguard(128, 160); irOptimized says memoryguard(0x08e0, 0xa0)
-- * `Halo2VerifyingKey`: ir says memoryguard(128); irOptimized says memoryguard(-) - the optimizer folds it out entirely
--
-- The deployed bytecode of Halo2Verifier begins PUSH2 0x08e0 PUSH1 0x40 MSTORE, which is what
-- Midfall.Generator.runtimeFreeMemoryPointerInit (Generator/Evm.lean:129) reads back, so the
-- shipped bytes agree with irOptimized and not with ir. That is deliberate: PLAN section 7
-- says irCheck validates the UNOPTIMISED IR, and the Yul-optimizer hop is explicitly in the
-- trusted base - covered by differential testing against the compiler, not proved here.
-- Pinning ir therefore puts the free-memory pointer at 0x80 where the deployed contract puts
-- it at 0x8e0. It is a memory-layout difference, and Bridge.ObsView deliberately excludes
-- memory, so it is not an observable difference at the level lowering_equivalence compares
-- at. verifierRuntime_head_is_memoryguard below states the pinned value propositionally, so
-- switching to irOptimized becomes a build failure and a decision rather than a silent drift.
-- Recorded again in docs/design.md D-P15.
--
-- ## DECISION 2: the two alpha-renames are applied at EMIT time
--
-- Lean's ident lexeme rejects the dollar sign and end is a reserved word, so the artifact
-- cannot be quoted as it stands. Emit-time renaming was chosen over extending the vendored DSL
-- lexer because (a) the lexer lives in vendor/, outside this package's authorisation; (b) a
-- lexer that accepts a dollar sign would make the DSL accept programs the upstream parser
-- rejects; and (c) either way the imported names differ from the artifact text, so the rename
-- has to be documented either way - and only the emit-time rename can be GATED from the
-- artifact. The rule is
--
--     x |-> "solc_" ++ x.replace "$" "_"      if x contains a dollar sign or x is reserved
--     x |-> x                                 otherwise
--
-- with the reserved list exactly `end`. That list is measured, not guessed: every
-- identifier of both artifacts was fed to yulE% and the rejections collected (517 of
-- 2246 distinct identifiers needed the rename). The other Lean keywords that occur in
-- the artifacts - if, let, for, switch, case, default, function, leave, object, code, data -
-- appear only in grammar positions the DSL already handles, and return only as the
-- return(...) statement, which has its own production; renaming those would break the
-- quotation rather than fix it. The mapping is auditable because the rule and the artifact are
-- both in the repo, and irRename_ok re-derives the whole mapping from the artifact text at
-- #eval time: injective, no image colliding with a name the rule leaves alone, no image that
-- is a Yul keyword, every renamed name actually present in the imported AST, and no original
-- name surviving anywhere in it.
--
-- ## What would not elaborate, and what was done about it (hazard 2)
--
-- Every construct the DSL cannot parse was found by elaborating the artifact, not by
-- reading the grammar. What the measurement found, per artifact:
--
-- * //-comments and the /// @src / /// @use-src annotations, for which the DSL has no
--   production: Halo2Verifier 48 lines, Halo2VerifyingKey 9 lines. Stripped at emit time.
-- * the dollar sign in identifiers, which Lean's ident lexeme rejects: Halo2Verifier 4580 occurrences in 514 distinct names, Halo2VerifyingKey 537 occurrences in 2 distinct names. Renamed by the rule above.
-- * the bare identifier end, which Lean reserves and solc uses as a parameter and return
--   name: Halo2Verifier 11 sites, Halo2VerifyingKey 0 sites. Renamed by the rule above.
-- * the type annotations : u256 and -> u256, which the DSL documents as unsupported: Halo2Verifier 0 occurrences, Halo2VerifyingKey 0 occurrences - so that documented deferral is not reached by this import. Measured, not hoped.
-- * hex string literals: Halo2Verifier 1 occurrence(s), Halo2VerifyingKey 1 occurrence(s) per artifact, every one of them a data segment, which the DSL does support.
-- * true as an identifier: Halo2Verifier 1 site(s), Halo2VerifyingKey 0 site(s), each a Yul boolean literal that the DSL maps to Literal.bool - no rename needed.
-- * return: Halo2Verifier 4 site(s), Halo2VerifyingKey 2 site(s), every one the return(...) statement, which has its own production, so it is not
--   renamed either and the reserved list stays exactly [end].
--
-- Reconciliation with the numbers docs/plans/P-VEND-dialect.md quotes: those were taken
-- from the DEPLOYED RUNTIME OBJECT alone (2,614 lines, 4,547 dollar signs, 6 end sites).
-- This import takes the whole ir object - creation plus deployed - because RunContractIR
-- reaches the runtime through Surface.irRuntime on the top-level object and because the
-- creation side is where setimmutable lives: 2,898 lines, 4,580 dollar signs, 11 end
-- sites, 514 distinct dollar names. The two sets of numbers describe nested artifacts,
-- not competing measurements.
--
-- NOTHING WAS DELETED TO MAKE THE BUILD PASS. The quotation below is the whole artifact,
-- comment-stripped and renamed; gates 2, 5, 6, 8 and 10 are what goes red if it were not -
-- gate 6 sees a deleted call, gate 8 sees a deleted node or a renamed identifier, gate 10
-- sees an edited literal. scripts/perturb_import_ir.py runs those controls on copies
-- outside the tree (R-41, R-54) and prints which gate reddens for which mutation. If a
-- future solc or a future template emits a construct the DSL cannot parse, this script's
-- output stops elaborating and the build fails loudly rather than importing less.
--
-- ## Not in this file
--
-- irCheck (PLAN section 7) and the lowering_equivalence statement itself: this package
-- supplies the object those consume. The RunContractIR witness lives in
-- Midfall/Instances/ImportedIR.lean, because a Surface needs an AdmissiblePairing and D-P17
-- keeps Instances/ out of theorem-bearing files.
-- GENERATED-BODY-BELOW

import YulSemantics
import YulSemantics.Ast
import YulSemantics.Syntax
import YulSemantics.Dialect.EVM
import Midfall.Yul.Builtins

-- A 2,900-line Yul object is one enormous Lean term: the quotation macro builds a right-nested
-- list literal of about a thousand statements, each with nested expression lists, and the
-- default recursion budget is exhausted by the elaborator and again by the compiler. The option
-- is set for this file only - it is a property of the artifact's size, not of the project - and
-- it is the only Lean-level concession the import makes.
set_option maxRecDepth 400000

namespace Midfall.Yul.Ir
open YulSemantics YulSemantics.EVM Midfall.Yul.Builtins

/-! ### The imported objects -/

/-- The ir artifact of proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2Verifier.sol, contract Halo2Verifier: solc textual
    via-IR, imported verbatim as a yulObject% quotation except for the two
    alpha-renames documented in this file header. Top-level object "Halo2Verifier_292", runtime sub-object
    "Halo2Verifier_292_deployed".

    sha256 of the committed artifact: a3e3923ecca9b4ebaaf2e357446d4a745b75fb2763c7a4a4c4f2e745aac1d109
    FNV-1a-64: 9842857077079826151   bytes: 192150   lines: 2898   dollar signs: 4580 -/

def verifierIr : Object EVM.Op := yulObject% 

object "Halo2Verifier_292" {
    code {
        
        mstore(64, memoryguard(160))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        let _1 := copy_arguments_for_constructor_273_object_Halo2Verifier_292()
        constructor_Halo2Verifier_292(_1)

        let _2 := allocate_unbounded()
        codecopy(_2, dataoffset("Halo2Verifier_292_deployed"), datasize("Halo2Verifier_292_deployed"))

        setimmutable(_2, "5", mload(128))

        return(_2, datasize("Halo2Verifier_292_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        function round_up_to_mul_of_32(value) -> result {
            result := and(add(value, 31), not(31))
        }

        function panic_error_0x41() {
            mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
            mstore(4, 0x41)
            revert(0, 0x24)
        }

        function finalize_allocation(memPtr, size) {
            let newFreePtr := add(memPtr, round_up_to_mul_of_32(size))
            
            if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
            mstore(64, newFreePtr)
        }

        function allocate_memory(size) -> memPtr {
            memPtr := allocate_unbounded()
            finalize_allocation(memPtr, size)
        }

        function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
            revert(0, 0)
        }

        function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
            revert(0, 0)
        }

        function cleanup_t_uint160(value) -> cleaned {
            cleaned := and(value, 0xffffffffffffffffffffffffffffffffffffffff)
        }

        function cleanup_t_address(value) -> cleaned {
            cleaned := cleanup_t_uint160(value)
        }

        function validator_revert_t_address(value) {
            if iszero(eq(value, cleanup_t_address(value))) { revert(0, 0) }
        }

        function abi_decode_t_address_fromMemory(offset, solc_end) -> value {
            value := mload(offset)
            validator_revert_t_address(value)
        }

        function abi_decode_tuple_t_address_fromMemory(headStart, dataEnd) -> value0 {
            if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            {

                let offset := 0

                value0 := abi_decode_t_address_fromMemory(add(headStart, offset), dataEnd)
            }

        }

        function copy_arguments_for_constructor_273_object_Halo2Verifier_292() -> ret_param_0 {

            let programSize := datasize("Halo2Verifier_292")
            let argSize := sub(codesize(), programSize)

            let memoryDataOffset := allocate_memory(argSize)
            codecopy(memoryDataOffset, programSize, argSize)

            ret_param_0 := abi_decode_tuple_t_address_fromMemory(memoryDataOffset, add(memoryDataOffset, argSize))
        }

        function cleanup_t_rational_17025_by_1(value) -> cleaned {
            cleaned := value
        }

        function cleanup_t_uint256(value) -> cleaned {
            cleaned := value
        }

        function identity(value) -> ret {
            ret := value
        }

        function convert_t_rational_17025_by_1_to_t_uint256(value) -> converted {
            converted := cleanup_t_uint256(identity(cleanup_t_rational_17025_by_1(value)))
        }

        
        function constant_EXPECTED_VK_LENGTH_11() -> ret {
            
            let expr_10 := 0x4281
            let _4 := convert_t_rational_17025_by_1_to_t_uint256(expr_10)

            ret := _4
        }

        function cleanup_t_rational_16401726817195526609941831384088918008201368669469322348229147391391451176969_by_1(value) -> cleaned {
            cleaned := value
        }

        function convert_t_rational_16401726817195526609941831384088918008201368669469322348229147391391451176969_by_1_to_t_uint256(value) -> converted {
            converted := cleanup_t_uint256(identity(cleanup_t_rational_16401726817195526609941831384088918008201368669469322348229147391391451176969_by_1(value)))
        }

        
        function constant_EXPECTED_VK_CODEHASH_WORD_14() -> ret {
            
            let expr_13 := 0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009
            let _6 := convert_t_rational_16401726817195526609941831384088918008201368669469322348229147391391451176969_by_1_to_t_uint256(expr_13)

            ret := _6
        }

        function cleanup_t_bytes32(value) -> cleaned {
            cleaned := value
        }

        function shift_left_0(value) -> newValue {
            newValue :=

            shl(0, value)

        }

        function convert_t_uint256_to_t_bytes32(value) -> converted {
            converted := cleanup_t_bytes32(shift_left_0(cleanup_t_uint256(value)))
        }

        
        function constant_EXPECTED_VK_CODEHASH_20() -> ret {
            
            let expr_18 := constant_EXPECTED_VK_CODEHASH_WORD_14()
            
            let expr_19 := convert_t_uint256_to_t_bytes32(expr_18)
            let _7 := expr_19

            ret := _7
        }

        function array_storeLengthForEncoding_t_string_memory_ptr_fromStack(pos, length) -> updated_pos {
            mstore(pos, length)
            updated_pos := add(pos, 0x20)
        }

        function store_literal_in_memory_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(memPtr) {

            mstore(add(memPtr, 0), "invalid vk")

        }

        function abi_encode_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf_to_t_string_memory_ptr_fromStack(pos) -> solc_end {
            pos := array_storeLengthForEncoding_t_string_memory_ptr_fromStack(pos, 10)
            store_literal_in_memory_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(pos)
            solc_end := add(pos, 32)
        }

        function abi_encode_tuple_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf__to_t_string_memory_ptr__fromStack(headStart ) -> tail {
            tail := add(headStart, 32)

            mstore(add(headStart, 0), sub(tail, headStart))
            tail := abi_encode_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf_to_t_string_memory_ptr_fromStack( tail)

        }

        function require_helper_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(condition ) {
            if iszero(condition)
            {

                let memPtr := allocate_unbounded()

                mstore(memPtr, 0x08c379a000000000000000000000000000000000000000000000000000000000)
                let solc_end := abi_encode_tuple_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf__to_t_string_memory_ptr__fromStack(add(memPtr, 4) )
                revert(memPtr, sub(solc_end, memPtr))
            }
        }

        
        
        function constructor_Halo2Verifier_292(var_authorizedVk_248) {

            

            fun_require_eip2537_precompiles_245()
            
            let _3 := var_authorizedVk_248
            let expr_255 := _3
            
            let expr_257 := extcodesize(expr_255)
            
            let expr_258 := constant_EXPECTED_VK_LENGTH_11()
            
            let expr_259 := eq(cleanup_t_uint256(expr_257), cleanup_t_uint256(expr_258))
            
            let expr_264 := expr_259
            if expr_264 {
                
                let _5 := var_authorizedVk_248
                let expr_260 := _5
                
                let expr_261 := extcodehash(expr_260)
                
                let expr_262 := constant_EXPECTED_VK_CODEHASH_20()
                
                let expr_263 := eq(cleanup_t_bytes32(expr_261), cleanup_t_bytes32(expr_262))
                
                expr_264 := expr_263
            }
            
            require_helper_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(expr_264)
            
            let _8 := var_authorizedVk_248
            let expr_269 := _8
            
            let _9 := expr_269
            mstore(128, _9)
            let expr_270 := expr_269

        }
        

        
        
        function fun_require_eip2537_precompiles_245() {

            
            {
                let solc_usr_scratch := 0x80
                mstore(solc_usr_scratch, 0x1234)
                mcopy(add(solc_usr_scratch, 0x20), solc_usr_scratch, 0x20)
                if iszero(eq(mload(add(solc_usr_scratch, 0x20)), 0x1234)) { revert(0, 0) }
                for { let solc_usr_off := 0 }
                lt(solc_usr_off, 0x0300)
                { solc_usr_off := add(solc_usr_off, 0x20) }
                {
                    mstore(add(solc_usr_scratch, solc_usr_off), 0)
                }
                if iszero(staticcall(gas(), 0x0b, solc_usr_scratch, 0x0100, solc_usr_scratch, 0x80)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
                if or(or(mload(solc_usr_scratch), mload(add(solc_usr_scratch, 0x20))), or(mload(add(solc_usr_scratch, 0x40)), mload(add(solc_usr_scratch, 0x60)))) { revert(0, 0) }
                let solc_usr_msm_scratch := 0xa1c0
                for { let solc_usr_off := 0 }
                lt(solc_usr_off, 0x30c0)
                { solc_usr_off := add(solc_usr_off, 0x20) }
                {
                    mstore(add(solc_usr_msm_scratch, solc_usr_off), 0)
                }
                if iszero(staticcall(gas(), 0x0c, solc_usr_msm_scratch, 0x30c0, solc_usr_scratch, 0x80)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
                if or(or(mload(solc_usr_scratch), mload(add(solc_usr_scratch, 0x20))), or(mload(add(solc_usr_scratch, 0x40)), mload(add(solc_usr_scratch, 0x60)))) { revert(0, 0) }
                if iszero(staticcall(gas(), 0x0f, solc_usr_scratch, 0x0300, solc_usr_scratch, 0x20)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
                if iszero(eq(mload(solc_usr_scratch), 1)) { revert(0, 0) }
            }

        }
        

    }
    
    object "Halo2Verifier_292_deployed" {
        code {
            
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x1e8e1e13
                {
                    

                    external_fun_verifyProof_291()
                }

                case 0x42b72597
                {
                    

                    external_fun_AUTHORIZED_VK_5()
                }

                default {}
            }

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
                revert(0, 0)
            }

            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() {
                revert(0, 0)
            }

            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
                revert(0, 0)
            }

            function revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() {
                revert(0, 0)
            }

            function revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() {
                revert(0, 0)
            }

            function revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() {
                revert(0, 0)
            }

            
            function abi_decode_t_bytes_calldata_ptr(offset, solc_end) -> arrayPos, length {
                if iszero(slt(add(offset, 0x1f), solc_end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x01)), solc_end) { revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() }
            }

            
            function solc_abi_decode_t_array__t_uint256__dyn_calldata_ptr(offset, solc_end) -> arrayPos, length {
                if iszero(slt(add(offset, 0x1f), solc_end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x20)), solc_end) { revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() }
            }

            function solc_abi_decode_tuple_t_bytes_calldata_ptrt_array__t_uint256__dyn_calldata_ptr(headStart, dataEnd) -> value0, value1, value2, value3 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := calldataload(add(headStart, 0))
                    if gt(offset, 0xffffffffffffffff) { revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() }

                    value0, value1 := abi_decode_t_bytes_calldata_ptr(add(headStart, offset), dataEnd)
                }

                {

                    let offset := calldataload(add(headStart, 32))
                    if gt(offset, 0xffffffffffffffff) { revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() }

                    value2, value3 := solc_abi_decode_t_array__t_uint256__dyn_calldata_ptr(add(headStart, offset), dataEnd)
                }

            }

            function cleanup_t_bool(value) -> cleaned {
                cleaned := iszero(iszero(value))
            }

            function abi_encode_t_bool_to_t_bool_fromStack(value, pos) {
                mstore(pos, cleanup_t_bool(value))
            }

            function abi_encode_tuple_t_bool__to_t_bool__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_bool_to_t_bool_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_verifyProof_291() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1, param_2, param_3 :=  solc_abi_decode_tuple_t_bytes_calldata_ptrt_array__t_uint256__dyn_calldata_ptr(4, calldatasize())
                let ret_0 :=  fun_verifyProof_291(param_0, param_1, param_2, param_3)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_bool__to_t_bool__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            
            
            function getter_fun_AUTHORIZED_VK_5() -> rval {

                rval := loadimmutable("5")

            }
            

            function cleanup_t_uint160(value) -> cleaned {
                cleaned := and(value, 0xffffffffffffffffffffffffffffffffffffffff)
            }

            function cleanup_t_address(value) -> cleaned {
                cleaned := cleanup_t_uint160(value)
            }

            function abi_encode_t_address_to_t_address_fromStack(value, pos) {
                mstore(pos, cleanup_t_address(value))
            }

            function abi_encode_tuple_t_address__to_t_address__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_address_to_t_address_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_AUTHORIZED_VK_5() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_AUTHORIZED_VK_5()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_address__to_t_address__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function zero_value_for_split_t_bool() -> ret {
                ret := 0
            }

            
            
            function fun_verifyProof_291(var_proof_276_offset, var_proof_276_length, var_instances_279_offset, var_instances_279_length) -> var__282 {
                
                let zero_t_bool_1 := zero_value_for_split_t_bool()
                var__282 := zero_t_bool_1

                
                {
                    if iszero(and(eq(calldataload(0x04), 0x40), eq(calldataload(0x24), sub(7876, 0x04)))) { revert(0, 0) }
                }
                
                let _2 := loadimmutable("5")
                let expr_287 := _2
                
                let var_vk_286 := expr_287
                
                {
                    function solc_usr_scalar_inv(solc_usr_x) -> solc_usr_inv
                    {
                        if iszero(solc_usr_x) { revert(0, 0) }
                        let solc_usr_p := 0x2600
                        mstore(add(solc_usr_p, 0x00), 0x20)
                        mstore(add(solc_usr_p, 0x20), 0x20)
                        mstore(add(solc_usr_p, 0x40), 0x20)
                        mstore(add(solc_usr_p, 0x60), solc_usr_x)
                        mstore(add(solc_usr_p, 0x80), sub(52435875175126190479447740508185965837690552500527637822603658699938581184513, 2))
                        mstore(add(solc_usr_p, 0xa0), 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                        if iszero(staticcall(gas(), 0x05, solc_usr_p, 0xc0, solc_usr_p, 0x20)) { revert(0, 0) }
                        if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
                        solc_usr_inv := mload(solc_usr_p)
                    }
                    function solc_usr_transcript_init() -> solc_usr_buf_len
                    { solc_usr_buf_len := 128 }
                    function solc_usr_common_word(solc_usr_buf_len, solc_usr_word) -> solc_usr_ret
                    {
                        mstore(solc_usr_buf_len, solc_usr_word)
                        solc_usr_ret := add(solc_usr_buf_len, 32)
                    }
                    function solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_cptr) -> solc_usr_ret
                    {
                        let solc_usr_x_hi_word := calldataload(solc_usr_cptr)
                        let solc_usr_x_lo := calldataload(add(solc_usr_cptr, 0x20))
                        let solc_usr_y_hi_word := calldataload(add(solc_usr_cptr, 0x40))
                        let solc_usr_y_lo := calldataload(add(solc_usr_cptr, 0x60))
                        if shr(128, solc_usr_x_hi_word) { revert(0, 0) }
                        if shr(128, solc_usr_y_hi_word) { revert(0, 0) }
                        let solc_usr_x_hi := and(solc_usr_x_hi_word, 0xffffffffffffffffffffffffffffffff)
                        let solc_usr_y_hi := and(solc_usr_y_hi_word, 0xffffffffffffffffffffffffffffffff)
                        if iszero(or(lt(solc_usr_x_hi, 34565483545414906068789196026815425751), and(eq(solc_usr_x_hi, 34565483545414906068789196026815425751), iszero(gt(solc_usr_x_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))))) { revert(0, 0) }
                        if iszero(or(lt(solc_usr_y_hi, 34565483545414906068789196026815425751), and(eq(solc_usr_y_hi, 34565483545414906068789196026815425751), iszero(gt(solc_usr_y_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))))) { revert(0, 0) }
                        calldatacopy(solc_usr_buf_len, solc_usr_cptr, 0x80)
                        solc_usr_ret := add(solc_usr_buf_len, 0x80)
                    }
                    function solc_usr_squeeze_to(solc_usr_buf_len, solc_usr_mptr) -> solc_usr_ret
                    {
                        let solc_usr_h0 := keccak256(128, sub(solc_usr_buf_len, 128))
                        mstore(128, solc_usr_h0)
                        let solc_usr_r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                        mstore(solc_usr_mptr, mod(solc_usr_h0, solc_usr_r))
                        solc_usr_ret := add(128, 32)
                    }
                    function solc_usr_batch_invert(solc_usr_success, solc_usr_mptr_start, solc_usr_mptr_end, solc_usr_scratch_mptr, solc_usr_r) -> solc_usr_ret
                    {
                        solc_usr_ret := solc_usr_success
                        if iszero(solc_usr_ret) { leave }
                        if lt(solc_usr_mptr_end, solc_usr_mptr_start)
                        {
                            solc_usr_ret := 0
                            leave
                        }
                        let solc_usr_count_bytes := sub(solc_usr_mptr_end, solc_usr_mptr_start)
                        if iszero(solc_usr_count_bytes) { leave }
                        if eq(solc_usr_count_bytes, 0x20)
                        {
                            let solc_usr_x := mload(solc_usr_mptr_start)
                            if iszero(solc_usr_x)
                            {
                                solc_usr_ret := 0
                                leave
                            }
                            let solc_usr_single_scratch := solc_usr_scratch_mptr
                            mstore(add(solc_usr_single_scratch, 0x00), 0x20)
                            mstore(add(solc_usr_single_scratch, 0x20), 0x20)
                            mstore(add(solc_usr_single_scratch, 0x40), 0x20)
                            mstore(add(solc_usr_single_scratch, 0x60), solc_usr_x)
                            mstore(add(solc_usr_single_scratch, 0x80), sub(solc_usr_r, 2))
                            mstore(add(solc_usr_single_scratch, 0xa0), solc_usr_r)
                            solc_usr_ret := staticcall(gas(), 0x05, solc_usr_single_scratch, 0xc0, solc_usr_single_scratch, 0x20)
                            solc_usr_ret := and(solc_usr_ret, eq(returndatasize(), 0x20))
                            if solc_usr_ret
                            {
                                mstore(solc_usr_mptr_start, mload(solc_usr_single_scratch))
                            }
                            leave
                        }
                        let solc_usr_gp_mptr := solc_usr_scratch_mptr
                        let solc_usr_gp := mload(solc_usr_mptr_start)
                        let solc_usr_mptr := add(solc_usr_mptr_start, 0x20)
                        for { } lt(solc_usr_mptr, sub(solc_usr_mptr_end, 0x20)) { }
                        {
                            solc_usr_gp := mulmod(solc_usr_gp, mload(solc_usr_mptr), solc_usr_r)
                            mstore(solc_usr_gp_mptr, solc_usr_gp)
                            solc_usr_mptr := add(solc_usr_mptr, 0x20)
                            solc_usr_gp_mptr := add(solc_usr_gp_mptr, 0x20)
                        }
                        solc_usr_gp := mulmod(solc_usr_gp, mload(solc_usr_mptr), solc_usr_r)
                        if iszero(solc_usr_gp)
                        {
                            solc_usr_ret := 0
                            leave
                        }
                        mstore(add(solc_usr_gp_mptr, 0x00), 0x20)
                        mstore(add(solc_usr_gp_mptr, 0x20), 0x20)
                        mstore(add(solc_usr_gp_mptr, 0x40), 0x20)
                        mstore(add(solc_usr_gp_mptr, 0x60), solc_usr_gp)
                        mstore(add(solc_usr_gp_mptr, 0x80), sub(solc_usr_r, 2))
                        mstore(add(solc_usr_gp_mptr, 0xa0), solc_usr_r)
                        solc_usr_ret := staticcall(gas(), 0x05, solc_usr_gp_mptr, 0xc0, solc_usr_gp_mptr, 0x20)
                        solc_usr_ret := and(solc_usr_ret, eq(returndatasize(), 0x20))
                        let solc_usr_all_inv := mload(solc_usr_gp_mptr)
                        let solc_usr_first_mptr := solc_usr_mptr_start
                        let solc_usr_second_mptr := add(solc_usr_first_mptr, 0x20)
                        solc_usr_gp_mptr := sub(solc_usr_gp_mptr, 0x20)
                        for { } lt(solc_usr_second_mptr, solc_usr_mptr) { }
                        {
                            let solc_usr_inv := mulmod(solc_usr_all_inv, mload(solc_usr_gp_mptr), solc_usr_r)
                            solc_usr_all_inv := mulmod(solc_usr_all_inv, mload(solc_usr_mptr), solc_usr_r)
                            mstore(solc_usr_mptr, solc_usr_inv)
                            solc_usr_mptr := sub(solc_usr_mptr, 0x20)
                            solc_usr_gp_mptr := sub(solc_usr_gp_mptr, 0x20)
                        }
                        let solc_usr_inv_first := mulmod(solc_usr_all_inv, mload(solc_usr_second_mptr), solc_usr_r)
                        let solc_usr_inv_second := mulmod(solc_usr_all_inv, mload(solc_usr_first_mptr), solc_usr_r)
                        mstore(solc_usr_first_mptr, solc_usr_inv_first)
                        mstore(solc_usr_second_mptr, solc_usr_inv_second)
                    }
                    function solc_usr_ec_pairing(solc_usr_success, solc_usr_lhs_mptr, solc_usr_rhs_mptr) -> solc_usr_ret
                    {
                        solc_usr_ret := solc_usr_success
                        if iszero(solc_usr_ret) { leave }
                        let solc_usr_scratch := 0x0300
                        mcopy(solc_usr_scratch, solc_usr_lhs_mptr, 0x80)
                        mcopy(add(solc_usr_scratch, 0x80), 10464, 0x100)
                        mcopy(add(solc_usr_scratch, 0x180), solc_usr_rhs_mptr, 0x80)
                        mcopy(add(solc_usr_scratch, 0x200), 10720, 0x100)
                        solc_usr_ret := staticcall(gas(), 0x0f, solc_usr_scratch, 0x0300, solc_usr_scratch, 0x20)
                        solc_usr_ret := and(solc_usr_ret, eq(returndatasize(), 0x20))
                        solc_usr_ret := and(solc_usr_ret, mload(solc_usr_scratch))
                        if iszero(solc_usr_ret) { revert(0, 0) }
                        solc_usr_ret := 1
                    }
                    function solc_usr_load_acc_coord_shifted(solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word, solc_usr_first_adjust) -> solc_usr_hi, solc_usr_lo
                    {
                        let solc_usr_mask := sub(solc_usr_base, 1)
                        for { let solc_usr_i := 0 }
                        lt(solc_usr_i, solc_usr_n)
                        { solc_usr_i := add(solc_usr_i, 1) }
                        {
                            let solc_usr_packed := calldataload(add(solc_usr_src, mul(div(solc_usr_i, solc_usr_limbs_per_word), 0x20)))
                            if and(iszero(div(solc_usr_i, solc_usr_limbs_per_word)), solc_usr_first_adjust)
                            {
                                solc_usr_packed := sub(solc_usr_packed, solc_usr_first_adjust)
                            }
                            let solc_usr_limb := and(shr(mul(mod(solc_usr_i, solc_usr_limbs_per_word), solc_usr_bits), solc_usr_packed), solc_usr_mask)
                            let solc_usr_shift := mul(solc_usr_i, solc_usr_bits)
                            if lt(solc_usr_shift, 256)
                            {
                                solc_usr_lo := add(solc_usr_lo, shl(solc_usr_shift, solc_usr_limb))
                                if gt(add(solc_usr_shift, solc_usr_bits), 256)
                                {
                                    solc_usr_hi := add(solc_usr_hi, shr(sub(256, solc_usr_shift), solc_usr_limb))
                                }
                            }
                            if iszero(lt(solc_usr_shift, 256))
                            {
                                solc_usr_hi := add(solc_usr_hi, shl(sub(solc_usr_shift, 256), solc_usr_limb))
                            }
                        }
                    }
                    function solc_usr_is_bls_p_minus_one(solc_usr_hi, solc_usr_lo) -> solc_usr_yes
                    {
                        solc_usr_yes := and(eq(solc_usr_hi, 34565483545414906068789196026815425751), eq(solc_usr_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))
                    }
                    function solc_usr_is_acc_encoded_identity(solc_usr_src) -> solc_usr_yes
                    {
                        solc_usr_yes := and(and(eq(calldataload(solc_usr_src), 25645630028331783532722944590531249665523018521732485735708912233130), eq(calldataload(add(solc_usr_src, 0x20)), 148457621397983152316361523253305392630546779012)), and(eq(calldataload(add(solc_usr_src, 0x40)), 25645630028331783532722944590531249665523018521732413678114874305194), eq(calldataload(add(solc_usr_src, 0x60)), 148457621397983152316361523253305392630546779012)))
                    }
                    function solc_usr_check_acc_coord_packing(solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_limbs_per_word) -> solc_usr_ok
                    {
                        solc_usr_ok := 1
                        let solc_usr_coord_words := div(add(solc_usr_n, sub(solc_usr_limbs_per_word, 1)), solc_usr_limbs_per_word)
                        for { let solc_usr_word_idx := 0 }
                        lt(solc_usr_word_idx, solc_usr_coord_words)
                        {
                            solc_usr_word_idx := add(solc_usr_word_idx, 1)
                        }
                        {
                            let solc_usr_remaining := sub(solc_usr_n, mul(solc_usr_word_idx, solc_usr_limbs_per_word))
                            let solc_usr_limbs_in_word := solc_usr_limbs_per_word
                            if lt(solc_usr_remaining, solc_usr_limbs_per_word)
                            {
                                solc_usr_limbs_in_word := solc_usr_remaining
                            }
                            let solc_usr_used_bits := mul(solc_usr_limbs_in_word, solc_usr_bits)
                            if lt(solc_usr_used_bits, 256)
                            {
                                solc_usr_ok := and(solc_usr_ok, lt(calldataload(add(solc_usr_src, mul(solc_usr_word_idx, 0x20))), shl(solc_usr_used_bits, 1)))
                            }
                        }
                    }
                    function solc_usr_load_acc_coord(solc_usr_src, solc_usr_allow_id, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word) -> solc_usr_ok, solc_usr_hi, solc_usr_lo, solc_usr_is_id
                    {
                        solc_usr_ok := solc_usr_check_acc_coord_packing(solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_limbs_per_word)
                        if and(solc_usr_allow_id, iszero(lt(calldataload(solc_usr_src), solc_usr_base)))
                        {
                            let solc_usr_adj_hi, solc_usr_adj_lo := solc_usr_load_acc_coord_shifted(solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word, solc_usr_base)
                            solc_usr_is_id := solc_usr_is_bls_p_minus_one(solc_usr_adj_hi, solc_usr_adj_lo)
                        }
                        solc_usr_hi, solc_usr_lo := solc_usr_load_acc_coord_shifted(solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word, mul(solc_usr_is_id, solc_usr_base))
                        solc_usr_ok := and(solc_usr_ok, or(lt(solc_usr_hi, 34565483545414906068789196026815425751), and(eq(solc_usr_hi, 34565483545414906068789196026815425751), iszero(gt(solc_usr_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850)))))
                        let solc_usr_was_p_minus_one := solc_usr_is_bls_p_minus_one(solc_usr_hi, solc_usr_lo)
                        if solc_usr_was_p_minus_one
                        {
                            solc_usr_hi := 0
                            solc_usr_lo := 0
                        }
                        if iszero(solc_usr_was_p_minus_one)
                        {
                            let solc_usr_next_lo := add(solc_usr_lo, 1)
                            solc_usr_hi := add(solc_usr_hi, lt(solc_usr_next_lo, solc_usr_lo))
                            solc_usr_lo := solc_usr_next_lo
                        }
                        solc_usr_ok := and(solc_usr_ok, lt(solc_usr_hi, shl(128, 1)))
                    }
                    function solc_usr_load_acc_point(solc_usr_dst, solc_usr_src, solc_usr_bits, solc_usr_n, solc_usr_base) -> solc_usr_ok, solc_usr_is_id
                    {
                        solc_usr_is_id := solc_usr_is_acc_encoded_identity(solc_usr_src)
                        if solc_usr_is_id
                        {
                            solc_usr_ok := 1
                            mstore(solc_usr_dst, 0)
                            mstore(add(solc_usr_dst, 0x20), 0)
                            mstore(add(solc_usr_dst, 0x40), 0)
                            mstore(add(solc_usr_dst, 0x60), 0)
                        }
                        if iszero(solc_usr_is_id)
                        {
                            let solc_usr_limbs_per_word := 4
                            let solc_usr_coord_words := div(add(solc_usr_n, sub(solc_usr_limbs_per_word, 1)), solc_usr_limbs_per_word)
                            let solc_usr_x_ok, solc_usr_x_hi, solc_usr_x_lo, solc_usr_x_is_id := solc_usr_load_acc_coord(solc_usr_src, 1, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word)
                            let solc_usr_y_ok, solc_usr_y_hi, solc_usr_y_lo, solc_usr_y_id := solc_usr_load_acc_coord(add(solc_usr_src, mul(solc_usr_coord_words, 0x20)), 0, solc_usr_bits, solc_usr_n, solc_usr_base, solc_usr_limbs_per_word)
                            pop(solc_usr_y_id)
                            solc_usr_ok := and(solc_usr_x_ok, solc_usr_y_ok)
                            solc_usr_is_id := solc_usr_x_is_id
                            if solc_usr_is_id
                            {
                                solc_usr_ok := and(solc_usr_ok, iszero(or(or(solc_usr_x_hi, solc_usr_x_lo), or(solc_usr_y_hi, solc_usr_y_lo))))
                                mstore(solc_usr_dst, 0)
                                mstore(add(solc_usr_dst, 0x20), 0)
                                mstore(add(solc_usr_dst, 0x40), 0)
                                mstore(add(solc_usr_dst, 0x60), 0)
                            }
                            if iszero(solc_usr_is_id)
                            {
                                let solc_usr_decoded_zero := iszero(or(or(solc_usr_x_hi, solc_usr_x_lo), or(solc_usr_y_hi, solc_usr_y_lo)))
                                solc_usr_ok := and(solc_usr_ok, iszero(solc_usr_decoded_zero))
                                mstore(solc_usr_dst, solc_usr_x_hi)
                                mstore(add(solc_usr_dst, 0x20), solc_usr_x_lo)
                                mstore(add(solc_usr_dst, 0x40), solc_usr_y_hi)
                                mstore(add(solc_usr_dst, 0x60), solc_usr_y_lo)
                            }
                        }
                    }
                    function solc_usr_validate_public_accumulator(solc_usr_success, solc_usr_r) -> solc_usr_out
                    {
                        solc_usr_out := solc_usr_success
                        let solc_usr_bits := 56
                        let solc_usr_n := 7
                        let solc_usr_limb_base := shl(solc_usr_bits, 1)
                        let solc_usr_limbs_per_word := 4
                        let solc_usr_coord_words := div(add(solc_usr_n, sub(solc_usr_limbs_per_word, 1)), solc_usr_limbs_per_word)
                        let solc_usr_acc_instance_ptr := add(7908, 0x0160)
                        let solc_usr_lhs_scalar_ptr := add(solc_usr_acc_instance_ptr, mul(mul(2, solc_usr_coord_words), 0x20))
                        let solc_usr_lhs_ok, solc_usr_lhs_is_id := solc_usr_load_acc_point(27584, solc_usr_acc_instance_ptr, solc_usr_bits, solc_usr_n, solc_usr_limb_base)
                        solc_usr_out := and(solc_usr_out, solc_usr_lhs_ok)
                        let solc_usr_acc_scratch := 0xa1c0
                        {
                            let solc_usr_lhs_scalar := 1
                            pop(solc_usr_lhs_is_id)
                            mcopy(solc_usr_acc_scratch, 27584, 0x80)
                            mstore(add(solc_usr_acc_scratch, 0x80), solc_usr_lhs_scalar)
                            if solc_usr_out
                            {
                                solc_usr_out := staticcall(gas(), 0x0c, solc_usr_acc_scratch, 0xa0, 27584, 0x80)
                                solc_usr_out := and(solc_usr_out, eq(returndatasize(), 0x80))
                            }
                        }
                        let solc_usr_rhs_instance_ptr := solc_usr_lhs_scalar_ptr
                        let solc_usr_rhs_scalar_ptr := add(solc_usr_rhs_instance_ptr, mul(mul(2, solc_usr_coord_words), 0x20))
                        let solc_usr_rhs_ok, solc_usr_rhs_is_id := solc_usr_load_acc_point(27712, solc_usr_rhs_instance_ptr, solc_usr_bits, solc_usr_n, solc_usr_limb_base)
                        solc_usr_out := and(solc_usr_out, solc_usr_rhs_ok)
                        let solc_usr_acc_pair_ptr := solc_usr_acc_scratch
                        {
                            let solc_usr_rhs_scalar := 1
                            pop(solc_usr_rhs_is_id)
                            mcopy(solc_usr_acc_pair_ptr, 27712, 0x80)
                            mstore(add(solc_usr_acc_pair_ptr, 0x80), solc_usr_rhs_scalar)
                            solc_usr_acc_pair_ptr := add(solc_usr_acc_pair_ptr, 0xa0)
                        }
                        let solc_usr_acc_msm_len := sub(solc_usr_acc_pair_ptr, solc_usr_acc_scratch)
                        if solc_usr_acc_msm_len
                        {
                            if solc_usr_out
                            {
                                solc_usr_out := staticcall(gas(), 0x0c, solc_usr_acc_scratch, solc_usr_acc_msm_len, 27712, 0x80)
                                solc_usr_out := and(solc_usr_out, eq(returndatasize(), 0x80))
                            }
                        }
                    }
                    let solc_usr_r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                    let solc_usr_success := true
                    {
                        if iszero(and(eq(extcodesize(var_vk_286), 17025), eq(extcodehash(var_vk_286), 16401726817195526609941831384088918008201368669469322348229147391391451176969))) { revert(0, 0) }
                        extcodecopy(var_vk_286, 9984, 0x01, 17024)
                        solc_usr_success := and(solc_usr_success, eq(mload(10016), 19))
                        solc_usr_success := and(solc_usr_success, eq(mload(10048), 20))
                        solc_usr_success := and(solc_usr_success, eq(mload(10208), 1))
                        solc_usr_success := and(solc_usr_success, eq(mload(10240), 11))
                        solc_usr_success := and(solc_usr_success, eq(mload(10272), 7))
                        solc_usr_success := and(solc_usr_success, eq(mload(10304), 56))
                        if iszero(solc_usr_success) { revert(0, 0) }
                        solc_usr_success := and(solc_usr_success, eq(0x1e60, calldataload(68)))
                        solc_usr_success := and(solc_usr_success, eq(19, calldataload(7876)))
                        solc_usr_success := and(solc_usr_success, eq(calldatasize(), add(7908, 0x0260)))
                        if iszero(solc_usr_success) { revert(0, 0) }
                    }
                    solc_usr_success := solc_usr_validate_public_accumulator(solc_usr_success, solc_usr_r)
                    if iszero(solc_usr_success) { revert(0, 0) }
                    let solc_usr_buf_len := solc_usr_transcript_init()
                    solc_usr_buf_len := solc_usr_common_word(solc_usr_buf_len, mload(9984))
                    {
                        mstore(solc_usr_buf_len, 0)
                        mstore(add(solc_usr_buf_len, 0x20), 0)
                        mstore(add(solc_usr_buf_len, 0x40), 0)
                        mstore(add(solc_usr_buf_len, 0x60), 0)
                        solc_usr_buf_len := add(solc_usr_buf_len, 0x80)
                    }
                    {
                        solc_usr_buf_len := solc_usr_common_word(solc_usr_buf_len, 19)
                        let solc_usr_instance_cptr := 7908
                        for {
                            let solc_usr_instance_cptr_end := add(solc_usr_instance_cptr, 0x0260)
                        }
                        lt(solc_usr_instance_cptr, solc_usr_instance_cptr_end)
                        {
                            solc_usr_instance_cptr := add(solc_usr_instance_cptr, 0x20)
                        }
                        {
                            let solc_usr_inst_be := calldataload(solc_usr_instance_cptr)
                            solc_usr_success := and(solc_usr_success, lt(solc_usr_inst_be, solc_usr_r))
                            solc_usr_buf_len := solc_usr_common_word(solc_usr_buf_len, solc_usr_inst_be)
                        }
                        if iszero(solc_usr_success) { revert(0, 0) }
                    }
                    let solc_usr_proof_cptr := 100
                    let solc_usr_advice_walk := 37312
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x0780)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_advice_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_advice_walk := add(solc_usr_advice_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27008)
                    let solc_usr_lookup_m_walk := 39232
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x0100)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_lookup_m_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_lookup_m_walk := add(solc_usr_lookup_m_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27040)
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27072)
                    let solc_usr_perm_z_walk := 39488
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x0300)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_perm_z_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_perm_z_walk := add(solc_usr_perm_z_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    let solc_usr_lookup_helper_walk := 40256
                    let solc_usr_lookup_z_walk := 40512
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x80)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_lookup_helper_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_lookup_helper_walk := add(solc_usr_lookup_helper_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                    calldatacopy(solc_usr_lookup_z_walk, solc_usr_proof_cptr, 0x80)
                    solc_usr_lookup_z_walk := add(solc_usr_lookup_z_walk, 0x80)
                    solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x80)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_lookup_helper_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_lookup_helper_walk := add(solc_usr_lookup_helper_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                    calldatacopy(solc_usr_lookup_z_walk, solc_usr_proof_cptr, 0x80)
                    solc_usr_lookup_z_walk := add(solc_usr_lookup_z_walk, 0x80)
                    solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27104)
                    let solc_usr_trashcan_walk := 40768
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x80)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_trashcan_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_trashcan_walk := add(solc_usr_trashcan_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27136)
                    let solc_usr_quotient_walk := 40896
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0x0200)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                        calldatacopy(solc_usr_quotient_walk, solc_usr_proof_cptr, 0x80)
                        solc_usr_quotient_walk := add(solc_usr_quotient_walk, 0x80)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27168)
                    {
                        let solc_usr_eval_buf := 34048
                        for {
                            let solc_usr_end := add(solc_usr_proof_cptr, 0x0cc0)
                        }
                        lt(solc_usr_proof_cptr, solc_usr_end)
                        { }
                        {
                            let solc_usr_eval := calldataload(solc_usr_proof_cptr)
                            if iszero(lt(solc_usr_eval, solc_usr_r)) { revert(0, 0) }
                            mstore(solc_usr_eval_buf, solc_usr_eval)
                            solc_usr_eval_buf := add(solc_usr_eval_buf, 0x20)
                            solc_usr_buf_len := solc_usr_common_word(solc_usr_buf_len, solc_usr_eval)
                            solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x20)
                        }
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27200)
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27232)
                    solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                    calldatacopy(27328, solc_usr_proof_cptr, 0x80)
                    solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27264)
                    mstore(27264, and(mload(27264), 0xffffffffffffffffffffffffffffffff))
                    mstore(33440, solc_usr_proof_cptr)
                    for {
                        let solc_usr_end := add(solc_usr_proof_cptr, 0xa0)
                    }
                    lt(solc_usr_proof_cptr, solc_usr_end)
                    { }
                    {
                        let solc_usr_eval := calldataload(solc_usr_proof_cptr)
                        if iszero(lt(solc_usr_eval, solc_usr_r)) { revert(0, 0) }
                        solc_usr_buf_len := solc_usr_common_word(solc_usr_buf_len, solc_usr_eval)
                        solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x20)
                    }
                    solc_usr_buf_len := solc_usr_squeeze_to(solc_usr_buf_len, 27296)
                    solc_usr_buf_len := solc_usr_common_uncompressed_g1(solc_usr_buf_len, solc_usr_proof_cptr)
                    calldatacopy(27456, solc_usr_proof_cptr, 0x80)
                    solc_usr_proof_cptr := add(solc_usr_proof_cptr, 0x80)
                    if iszero(eq(solc_usr_proof_cptr, 7876)) { revert(0, 0) }
                    if iszero(solc_usr_success) { revert(0, 0) }
                    {
                        let solc_usr_k := 20
                        let solc_usr_x := mload(27168)
                        let solc_usr_x_n := solc_usr_x
                        for { let solc_usr_idx := 0 }
                        lt(solc_usr_idx, solc_usr_k)
                        { solc_usr_idx := add(solc_usr_idx, 1) }
                        {
                            solc_usr_x_n := mulmod(solc_usr_x_n, solc_usr_x_n, solc_usr_r)
                        }
                        let solc_usr_omega := mload(10112)
                        let solc_usr_mptr := 27840
                        let solc_usr_mptr_end := add(solc_usr_mptr, 0x03a0)
                        for {
                            let solc_usr_pow_of_omega := mload(10176)
                        }
                        lt(solc_usr_mptr, solc_usr_mptr_end)
                        {
                            solc_usr_mptr := add(solc_usr_mptr, 0x20)
                        }
                        {
                            mstore(solc_usr_mptr, addmod(solc_usr_x, sub(solc_usr_r, solc_usr_pow_of_omega), solc_usr_r))
                            solc_usr_pow_of_omega := mulmod(solc_usr_pow_of_omega, solc_usr_omega, solc_usr_r)
                        }
                        let solc_usr_x_n_minus_1 := addmod(solc_usr_x_n, sub(solc_usr_r, 1), solc_usr_r)
                        mstore(solc_usr_mptr_end, solc_usr_x_n_minus_1)
                        solc_usr_success := solc_usr_batch_invert(solc_usr_success, 27840, add(solc_usr_mptr_end, 0x20), 41408, solc_usr_r)
                        solc_usr_mptr := 27840
                        let solc_usr_l_i_common := mulmod(solc_usr_x_n_minus_1, mload(10080), solc_usr_r)
                        for {
                            let solc_usr_pow_of_omega := mload(10176)
                        }
                        lt(solc_usr_mptr, solc_usr_mptr_end)
                        {
                            solc_usr_mptr := add(solc_usr_mptr, 0x20)
                        }
                        {
                            mstore(solc_usr_mptr, mulmod(solc_usr_l_i_common, mulmod(mload(solc_usr_mptr), solc_usr_pow_of_omega, solc_usr_r), solc_usr_r))
                            solc_usr_pow_of_omega := mulmod(solc_usr_pow_of_omega, solc_usr_omega, solc_usr_r)
                        }
                        let solc_usr_l_blind := mload(add(27840, 0x20))
                        let solc_usr_l_i_cptr := add(27840, 0x40)
                        for {
                            let solc_usr_l_i_cptr_end := add(27840, 0x0140)
                        }
                        lt(solc_usr_l_i_cptr, solc_usr_l_i_cptr_end)
                        {
                            solc_usr_l_i_cptr := add(solc_usr_l_i_cptr, 0x20)
                        }
                        {
                            solc_usr_l_blind := addmod(solc_usr_l_blind, mload(solc_usr_l_i_cptr), solc_usr_r)
                        }
                        let solc_usr_instance_eval := 0
                        for {
                            let solc_usr_instance_cptr := 7908
                            let solc_usr_instance_cptr_end := add(solc_usr_instance_cptr, 0x0260)
                        }
                        lt(solc_usr_instance_cptr, solc_usr_instance_cptr_end)
                        {
                            solc_usr_instance_cptr := add(solc_usr_instance_cptr, 0x20)
                            solc_usr_l_i_cptr := add(solc_usr_l_i_cptr, 0x20)
                        }
                        {
                            solc_usr_instance_eval := addmod(solc_usr_instance_eval, mulmod(mload(solc_usr_l_i_cptr), calldataload(solc_usr_instance_cptr), solc_usr_r), solc_usr_r)
                        }
                        let solc_usr_x_n_minus_1_inv := mload(solc_usr_mptr_end)
                        let solc_usr_l_last := mload(27840)
                        let solc_usr_l_0 := mload(add(27840, 0x0140))
                        mstore(27840, solc_usr_x_n)
                        mstore(27872, solc_usr_x_n_minus_1_inv)
                        mstore(27904, solc_usr_l_last)
                        mstore(27936, solc_usr_l_blind)
                        mstore(27968, solc_usr_l_0)
                        mstore(28000, solc_usr_instance_eval)
                    }
                    if iszero(solc_usr_success) { revert(0, 0) }
                    function solc_usr_q_pow5(solc_usr_x) -> solc_usr_z
                    {
                        let solc_usr_q_r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                        let solc_usr_x2 := mulmod(solc_usr_x, solc_usr_x, solc_usr_q_r)
                        solc_usr_z := mulmod(solc_usr_x, mulmod(solc_usr_x2, solc_usr_x2, solc_usr_q_r), solc_usr_q_r)
                    }
                    {
                        let solc_usr_y := mload(27136)
                        let solc_usr_q_const_mptr := 0x2ae0
                        let solc_usr_q_program_mptr := 0x4120
                        mstore(0xa300, 0)
                        for { let solc_usr_q_sel_zero_off := 0 }
                        lt(solc_usr_q_sel_zero_off, 0x0140)
                        {
                            solc_usr_q_sel_zero_off := add(solc_usr_q_sel_zero_off, 0x20)
                        }
                        {
                            mstore(add(41408, solc_usr_q_sel_zero_off), 0)
                        }
                        {
                            let solc_usr_q_y_power := 1
                            for { let solc_usr_q_y_power_i := 1 }
                            lt(solc_usr_q_y_power_i, 49)
                            {
                                solc_usr_q_y_power_i := add(solc_usr_q_y_power_i, 1)
                            }
                            {
                                solc_usr_q_y_power := mulmod(solc_usr_q_y_power, solc_usr_y, solc_usr_r)
                                mstore(add(0xa340, shl(5, solc_usr_q_y_power_i)), solc_usr_q_y_power)
                            }
                        }
                        {
                            let solc_usr_var0 := 0x1
                            let solc_usr_f_3 := mload(0x8b40)
                            let solc_usr_f_4 := mload(0x8a40)
                            let solc_usr_a_0 := mload(0x8520)
                            let solc_usr_var1 := mulmod(solc_usr_f_4, solc_usr_a_0, solc_usr_r)
                            let solc_usr_var2 := addmod(solc_usr_f_3, solc_usr_var1, solc_usr_r)
                            let solc_usr_f_5 := mload(0x8a60)
                            let solc_usr_a_1 := mload(0x8540)
                            let solc_usr_var3 := mulmod(solc_usr_f_5, solc_usr_a_1, solc_usr_r)
                            let solc_usr_var4 := addmod(solc_usr_var2, solc_usr_var3, solc_usr_r)
                            let solc_usr_f_6 := mload(0x8a80)
                            let solc_usr_a_2 := mload(0x8560)
                            let solc_usr_var5 := mulmod(solc_usr_f_6, solc_usr_a_2, solc_usr_r)
                            let solc_usr_var6 := addmod(solc_usr_var4, solc_usr_var5, solc_usr_r)
                            let solc_usr_f_7 := mload(0x8aa0)
                            let solc_usr_a_3 := mload(0x8580)
                            let solc_usr_var7 := mulmod(solc_usr_f_7, solc_usr_a_3, solc_usr_r)
                            let solc_usr_var8 := addmod(solc_usr_var6, solc_usr_var7, solc_usr_r)
                            let solc_usr_f_8 := mload(0x8ac0)
                            let solc_usr_a_4 := mload(0x85a0)
                            let solc_usr_var9 := mulmod(solc_usr_f_8, solc_usr_a_4, solc_usr_r)
                            let solc_usr_var10 := addmod(solc_usr_var8, solc_usr_var9, solc_usr_r)
                            let solc_usr_f_0 := mload(0x8ae0)
                            let solc_usr_a_0_next_1 := mload(0x85c0)
                            let solc_usr_var11 := mulmod(solc_usr_f_0, solc_usr_a_0_next_1, solc_usr_r)
                            let solc_usr_var12 := addmod(solc_usr_var10, solc_usr_var11, solc_usr_r)
                            let solc_usr_f_1 := mload(0x8b00)
                            let solc_usr_var13 := mulmod(solc_usr_f_1, solc_usr_a_0, solc_usr_r)
                            let solc_usr_var14 := mulmod(solc_usr_var13, solc_usr_a_1, solc_usr_r)
                            let solc_usr_var15 := addmod(solc_usr_var12, solc_usr_var14, solc_usr_r)
                            let solc_usr_f_2 := mload(0x8b20)
                            let solc_usr_var16 := mulmod(solc_usr_f_2, solc_usr_a_0, solc_usr_r)
                            let solc_usr_var17 := mulmod(solc_usr_var16, solc_usr_a_2, solc_usr_r)
                            let solc_usr_var18 := addmod(solc_usr_var15, solc_usr_var17, solc_usr_r)
                            let solc_usr_var19 := mulmod(solc_usr_var0, solc_usr_var18, solc_usr_r)
                            mstore(0xa960, solc_usr_var19)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                        {
                            let solc_usr_q_selector_ptr := add(41408, 0x0)
                            let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                            mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                        }
                        {
                            let solc_usr_var0 := 0x1
                            let solc_usr_a_1 := mload(0x8540)
                            let solc_usr_a_2 := mload(0x8560)
                            let solc_usr_var1 := addmod(solc_usr_a_1, solc_usr_a_2, solc_usr_r)
                            let solc_usr_a_3 := mload(0x8580)
                            let solc_usr_var2 := addmod(0, sub(solc_usr_r, solc_usr_a_3), solc_usr_r)
                            let solc_usr_var3 := addmod(solc_usr_var1, solc_usr_var2, solc_usr_r)
                            let solc_usr_a_4 := mload(0x85a0)
                            let solc_usr_var4 := addmod(0, sub(solc_usr_r, solc_usr_a_4), solc_usr_r)
                            let solc_usr_var5 := addmod(solc_usr_var3, solc_usr_var4, solc_usr_r)
                            let solc_usr_var6 := mulmod(solc_usr_var0, solc_usr_var5, solc_usr_r)
                            mstore(0xa960, solc_usr_var6)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                        {
                            let solc_usr_q_selector_ptr := add(41408, 0x20)
                            let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                            mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                        }
                        {
                            let solc_usr_var0 := 0x1
                            let solc_usr_a_0 := mload(0x8520)
                            let solc_usr_f_4 := mload(0x8a40)
                            let solc_usr_var1 := addmod(solc_usr_a_0, solc_usr_f_4, solc_usr_r)
                            let solc_usr_a_0_next_1 := mload(0x85c0)
                            let solc_usr_var2 := addmod(0, sub(solc_usr_r, solc_usr_a_0_next_1), solc_usr_r)
                            let solc_usr_var3 := addmod(solc_usr_var1, solc_usr_var2, solc_usr_r)
                            let solc_usr_var4 := mulmod(solc_usr_var0, solc_usr_var3, solc_usr_r)
                            mstore(0xa960, solc_usr_var4)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                        {
                            let solc_usr_q_selector_ptr := add(41408, 0x40)
                            let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                            mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                        }
                        {
                            let solc_usr_var0 := 0x1
                            let solc_usr_a_1 := mload(0x8540)
                            let solc_usr_f_5 := mload(0x8a60)
                            let solc_usr_var1 := addmod(solc_usr_a_1, solc_usr_f_5, solc_usr_r)
                            let solc_usr_a_1_next_1 := mload(0x85e0)
                            let solc_usr_var2 := addmod(0, sub(solc_usr_r, solc_usr_a_1_next_1), solc_usr_r)
                            let solc_usr_var3 := addmod(solc_usr_var1, solc_usr_var2, solc_usr_r)
                            let solc_usr_var4 := mulmod(solc_usr_var0, solc_usr_var3, solc_usr_r)
                            mstore(0xa960, solc_usr_var4)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                        {
                            let solc_usr_q_selector_ptr := add(41408, 0x40)
                            let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                            solc_usr_q_selector_acc := mulmod(solc_usr_q_selector_acc, mload(add(0xa340, 0x20)), solc_usr_r)
                            mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                        }
                        let solc_usr_q_pc := solc_usr_q_program_mptr
                        let solc_usr_q_end := add(solc_usr_q_program_mptr, 0x11cf)
                        let solc_usr_q_sp := 0xa960
                        let solc_usr_q_top := 0
                        let solc_usr_q_has_top := 0
                        for { } lt(solc_usr_q_pc, solc_usr_q_end) { }
                        {
                            let solc_usr_q_op := byte(0, mload(solc_usr_q_pc))
                            solc_usr_q_pc := add(solc_usr_q_pc, 1)
                            switch solc_usr_q_op
                            case 0x05 {
                                let solc_usr_q_ptr := shr(240, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                if solc_usr_q_has_top
                                {
                                    mstore(solc_usr_q_sp, solc_usr_q_top)
                                    solc_usr_q_sp := add(solc_usr_q_sp, 0x20)
                                }
                                solc_usr_q_top := mload(solc_usr_q_ptr)
                                solc_usr_q_has_top := 1
                            }
                            case 0x06 {
                                solc_usr_q_sp := sub(solc_usr_q_sp, 0x20)
                                solc_usr_q_top := addmod(mload(solc_usr_q_sp), solc_usr_q_top, solc_usr_r)
                            }
                            case 0x08 {
                                solc_usr_q_top := addmod(0, sub(solc_usr_r, solc_usr_q_top), solc_usr_r)
                            }
                            case 0x0d {
                                let solc_usr_qconst := byte(0, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 1)
                                solc_usr_q_top := mulmod(solc_usr_q_top, mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), solc_usr_r)
                            }
                            case 0x10 {
                                let solc_usr_q_ptr := shr(240, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                solc_usr_q_top := addmod(solc_usr_q_top, mload(solc_usr_q_ptr), solc_usr_r)
                            }
                            case 0x11 {
                                let solc_usr_q_ptr := shr(240, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                solc_usr_q_top := mulmod(solc_usr_q_top, mload(solc_usr_q_ptr), solc_usr_r)
                            }
                            case 0x21 {
                                let solc_usr_q_flags := byte(0, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 1)
                                let solc_usr_q_cond_ptr := 0
                                if and(solc_usr_q_flags, 0x01)
                                {
                                    solc_usr_q_cond_ptr := shr(240, mload(solc_usr_q_pc))
                                    solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                }
                                let solc_usr_q_acc := 0
                                if and(solc_usr_q_flags, 0x02)
                                {
                                    let solc_usr_qconst := byte(0, mload(solc_usr_q_pc))
                                    solc_usr_q_pc := add(solc_usr_q_pc, 1)
                                    solc_usr_q_acc := mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst)))
                                }
                                let solc_usr_q_counts_word := mload(solc_usr_q_pc)
                                let solc_usr_q_lin_count := byte(0, solc_usr_q_counts_word)
                                let solc_usr_q_row_count := byte(1, solc_usr_q_counts_word)
                                let solc_usr_q_pairwise_count := byte(2, solc_usr_q_counts_word)
                                let solc_usr_q_mem_count := byte(3, solc_usr_q_counts_word)
                                let solc_usr_q_product_count := byte(4, solc_usr_q_counts_word)
                                solc_usr_q_pc := add(solc_usr_q_pc, 5)
                                if solc_usr_q_has_top
                                {
                                    mstore(solc_usr_q_sp, solc_usr_q_top)
                                    solc_usr_q_sp := add(solc_usr_q_sp, 0x20)
                                }
                                for { let solc_usr_q_lin_block := 0 }
                                lt(solc_usr_q_lin_block, solc_usr_q_lin_count)
                                {
                                    solc_usr_q_lin_block := add(solc_usr_q_lin_block, 1)
                                }
                                {
                                    for { let solc_usr_q_i := 0 }
                                    lt(solc_usr_q_i, 7)
                                    { solc_usr_q_i := add(solc_usr_q_i, 1) }
                                    {
                                        let solc_usr_q_word := mload(solc_usr_q_pc)
                                        let solc_usr_qconst := byte(0, solc_usr_q_word)
                                        let solc_usr_q_ptr := and(shr(232, solc_usr_q_word), 0xffff)
                                        solc_usr_q_pc := add(solc_usr_q_pc, 3)
                                        solc_usr_q_acc := addmod(solc_usr_q_acc, mulmod(mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), mload(solc_usr_q_ptr), solc_usr_r), solc_usr_r)
                                    }
                                }
                                for { let solc_usr_q_row_block := 0 }
                                lt(solc_usr_q_row_block, solc_usr_q_row_count)
                                {
                                    solc_usr_q_row_block := add(solc_usr_q_row_block, 1)
                                }
                                {
                                    let solc_usr_q_lhs := shr(240, mload(solc_usr_q_pc))
                                    solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                    let solc_usr_q_lhs_value := mload(solc_usr_q_lhs)
                                    for { let solc_usr_q_i := 0 }
                                    lt(solc_usr_q_i, 7)
                                    { solc_usr_q_i := add(solc_usr_q_i, 1) }
                                    {
                                        let solc_usr_q_word := mload(solc_usr_q_pc)
                                        let solc_usr_qconst := byte(0, solc_usr_q_word)
                                        let solc_usr_q_rhs := and(shr(232, solc_usr_q_word), 0xffff)
                                        solc_usr_q_pc := add(solc_usr_q_pc, 3)
                                        solc_usr_q_acc := addmod(solc_usr_q_acc, mulmod(mulmod(solc_usr_q_lhs_value, mload(solc_usr_q_rhs), solc_usr_r), mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), solc_usr_r), solc_usr_r)
                                    }
                                }
                                for { let solc_usr_q_pair_block := 0 }
                                lt(solc_usr_q_pair_block, solc_usr_q_pairwise_count)
                                {
                                    solc_usr_q_pair_block := add(solc_usr_q_pair_block, 1)
                                }
                                {
                                    let solc_usr_q_pair_word := mload(solc_usr_q_pc)
                                    let solc_usr_q_lhs_base := shr(240, solc_usr_q_pair_word)
                                    let solc_usr_q_rhs_base := and(shr(224, solc_usr_q_pair_word), 0xffff)
                                    solc_usr_q_pc := add(solc_usr_q_pc, 0x04)
                                    let solc_usr_q_coeff_pc := solc_usr_q_pc
                                    solc_usr_q_pc := add(solc_usr_q_pc, 13)
                                    for { let solc_usr_q_i := 0 }
                                    lt(solc_usr_q_i, 7)
                                    { solc_usr_q_i := add(solc_usr_q_i, 1) }
                                    {
                                        let solc_usr_q_lhs_value := mload(add(solc_usr_q_lhs_base, shl(5, solc_usr_q_i)))
                                        for { let solc_usr_q_j := 0 }
                                        lt(solc_usr_q_j, 7)
                                        { solc_usr_q_j := add(solc_usr_q_j, 1) }
                                        {
                                            let solc_usr_qconst := byte(0, mload(add(solc_usr_q_coeff_pc, add(solc_usr_q_i, solc_usr_q_j))))
                                            solc_usr_q_acc := addmod(solc_usr_q_acc, mulmod(mulmod(solc_usr_q_lhs_value, mload(add(solc_usr_q_rhs_base, shl(5, solc_usr_q_j))), solc_usr_r), mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), solc_usr_r), solc_usr_r)
                                        }
                                    }
                                }
                                for { let solc_usr_q_mem_block := 0 }
                                lt(solc_usr_q_mem_block, solc_usr_q_mem_count)
                                {
                                    solc_usr_q_mem_block := add(solc_usr_q_mem_block, 1)
                                }
                                {
                                    let solc_usr_q_word := mload(solc_usr_q_pc)
                                    let solc_usr_qconst := byte(0, solc_usr_q_word)
                                    let solc_usr_q_ptr := and(shr(232, solc_usr_q_word), 0xffff)
                                    solc_usr_q_pc := add(solc_usr_q_pc, 3)
                                    solc_usr_q_acc := addmod(solc_usr_q_acc, mulmod(mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), mload(solc_usr_q_ptr), solc_usr_r), solc_usr_r)
                                }
                                for { let solc_usr_q_product_block := 0 }
                                lt(solc_usr_q_product_block, solc_usr_q_product_count)
                                {
                                    solc_usr_q_product_block := add(solc_usr_q_product_block, 1)
                                }
                                {
                                    let solc_usr_q_word := mload(solc_usr_q_pc)
                                    let solc_usr_qconst := byte(0, solc_usr_q_word)
                                    let solc_usr_q_lhs := and(shr(232, solc_usr_q_word), 0xffff)
                                    let solc_usr_q_rhs := and(shr(216, solc_usr_q_word), 0xffff)
                                    solc_usr_q_pc := add(solc_usr_q_pc, 5)
                                    solc_usr_q_acc := addmod(solc_usr_q_acc, mulmod(mulmod(mload(solc_usr_q_lhs), mload(solc_usr_q_rhs), solc_usr_r), mload(add(solc_usr_q_const_mptr, shl(5, solc_usr_qconst))), solc_usr_r), solc_usr_r)
                                }
                                if and(solc_usr_q_flags, 0x01)
                                {
                                    solc_usr_q_acc := mulmod(mload(solc_usr_q_cond_ptr), solc_usr_q_acc, solc_usr_r)
                                }
                                solc_usr_q_top := solc_usr_q_acc
                                solc_usr_q_has_top := 1
                            }
                            case 0x19 {
                                solc_usr_q_top := 0
                                solc_usr_q_has_top := 0
                                solc_usr_q_sp := 0xa960
                                {
                                    let solc_usr_delta := 0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
                                    let solc_usr_q_perm_vals := 0xa960
                                    let solc_usr_q_perm_sigmas := 0xaba0
                                    let solc_usr_q_perm_z_cur := 0xade0
                                    let solc_usr_q_perm_z_next := 0xaea0
                                    let solc_usr_q_perm_z_last := 0xaf60
                                    let solc_usr_q_perm_delta_base_ptr := 0xb000
                                    let solc_usr_q_perm_num_cols := 18
                                    let solc_usr_q_perm_num_sets := 6
                                    let solc_usr_q_perm_chunk_len := 3
                                    let solc_usr_q_perm_delta_chunk := 0x4285088329c399ea457a8ca1d30f8957e74c7f529842a1579b4fee55b3982923
                                    mstore(add(solc_usr_q_perm_vals, 0x0), mload(0x8a20))
                                    {
                                        for {
                                            let solc_usr_q_perm_val_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_val_load_i, 5)
                                        {
                                            solc_usr_q_perm_val_load_i := add(solc_usr_q_perm_val_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_val_load_dst_off := shl(5, solc_usr_q_perm_val_load_i)
                                            let solc_usr_q_perm_val_load_src_off := solc_usr_q_perm_val_load_dst_off
                                            mstore(add(add(solc_usr_q_perm_vals, 0x20), solc_usr_q_perm_val_load_dst_off), mload(add(0x8520, solc_usr_q_perm_val_load_src_off)))
                                        }
                                    }
                                    mstore(add(solc_usr_q_perm_vals, 0xc0), mload(0x8500))
                                    mstore(add(solc_usr_q_perm_vals, 0xe0), mload(28000))
                                    {
                                        for {
                                            let solc_usr_q_perm_val_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_val_load_i, 9)
                                        {
                                            solc_usr_q_perm_val_load_i := add(solc_usr_q_perm_val_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_val_load_dst_off := shl(5, solc_usr_q_perm_val_load_i)
                                            let solc_usr_q_perm_val_load_src_off := solc_usr_q_perm_val_load_dst_off
                                            mstore(add(add(solc_usr_q_perm_vals, 0x100), solc_usr_q_perm_val_load_dst_off), mload(add(0x8620, solc_usr_q_perm_val_load_src_off)))
                                        }
                                    }
                                    mstore(add(solc_usr_q_perm_vals, 0x220), mload(0x8a00))
                                    {
                                        for {
                                            let solc_usr_q_perm_sigma_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_sigma_load_i, 18)
                                        {
                                            solc_usr_q_perm_sigma_load_i := add(solc_usr_q_perm_sigma_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_sigma_load_dst_off := shl(5, solc_usr_q_perm_sigma_load_i)
                                            let solc_usr_q_perm_sigma_load_src_off := solc_usr_q_perm_sigma_load_dst_off
                                            mstore(add(add(solc_usr_q_perm_sigmas, 0x0), solc_usr_q_perm_sigma_load_dst_off), mload(add(0x8c40, solc_usr_q_perm_sigma_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let solc_usr_q_perm_z_cur_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_z_cur_load_i, 6)
                                        {
                                            solc_usr_q_perm_z_cur_load_i := add(solc_usr_q_perm_z_cur_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_z_cur_load_dst_off := shl(5, solc_usr_q_perm_z_cur_load_i)
                                            let solc_usr_q_perm_z_cur_load_src_off := mul(solc_usr_q_perm_z_cur_load_i, 0x60)
                                            mstore(add(add(solc_usr_q_perm_z_cur, 0x0), solc_usr_q_perm_z_cur_load_dst_off), mload(add(0x8e80, solc_usr_q_perm_z_cur_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let solc_usr_q_perm_z_next_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_z_next_load_i, 6)
                                        {
                                            solc_usr_q_perm_z_next_load_i := add(solc_usr_q_perm_z_next_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_z_next_load_dst_off := shl(5, solc_usr_q_perm_z_next_load_i)
                                            let solc_usr_q_perm_z_next_load_src_off := mul(solc_usr_q_perm_z_next_load_i, 0x60)
                                            mstore(add(add(solc_usr_q_perm_z_next, 0x0), solc_usr_q_perm_z_next_load_dst_off), mload(add(0x8ea0, solc_usr_q_perm_z_next_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let solc_usr_q_perm_z_last_load_i := 0
                                        }
                                        lt(solc_usr_q_perm_z_last_load_i, 5)
                                        {
                                            solc_usr_q_perm_z_last_load_i := add(solc_usr_q_perm_z_last_load_i, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_z_last_load_dst_off := shl(5, solc_usr_q_perm_z_last_load_i)
                                            let solc_usr_q_perm_z_last_load_src_off := mul(solc_usr_q_perm_z_last_load_i, 0x60)
                                            mstore(add(add(solc_usr_q_perm_z_last, 0x0), solc_usr_q_perm_z_last_load_dst_off), mload(add(0x8ec0, solc_usr_q_perm_z_last_load_src_off)))
                                        }
                                    }
                                    let solc_usr_q_perm_eval := 0
                                    solc_usr_q_perm_eval := mulmod(mload(27968), addmod(1, sub(solc_usr_r, mload(solc_usr_q_perm_z_cur)), solc_usr_r), solc_usr_r)
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    mstore(0xa300, addmod(mload(0xa300), solc_usr_q_perm_eval, solc_usr_r))
                                    let solc_usr_q_perm_zn := mload(add(solc_usr_q_perm_z_cur, 0xa0))
                                    solc_usr_q_perm_eval := mulmod(mload(27904), addmod(mulmod(solc_usr_q_perm_zn, solc_usr_q_perm_zn, solc_usr_r), sub(solc_usr_r, solc_usr_q_perm_zn), solc_usr_r), solc_usr_r)
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    mstore(0xa300, addmod(mload(0xa300), solc_usr_q_perm_eval, solc_usr_r))
                                    for { let solc_usr_q_perm_i := 1 }
                                    lt(solc_usr_q_perm_i, 6)
                                    {
                                        solc_usr_q_perm_i := add(solc_usr_q_perm_i, 1)
                                    }
                                    {
                                        let solc_usr_q_perm_cur := mload(add(solc_usr_q_perm_z_cur, shl(5, solc_usr_q_perm_i)))
                                        let solc_usr_q_perm_prev := mload(add(solc_usr_q_perm_z_last, shl(5, sub(solc_usr_q_perm_i, 1))))
                                        solc_usr_q_perm_eval := mulmod(mload(27968), addmod(solc_usr_q_perm_cur, sub(solc_usr_r, solc_usr_q_perm_prev), solc_usr_r), solc_usr_r)
                                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                        mstore(0xa300, addmod(mload(0xa300), solc_usr_q_perm_eval, solc_usr_r))
                                    }
                                    mstore(solc_usr_q_perm_delta_base_ptr, mulmod(mload(27040), mload(27168), solc_usr_r))
                                    for { let solc_usr_q_perm_set := 0 }
                                    lt(solc_usr_q_perm_set, 6)
                                    {
                                        solc_usr_q_perm_set := add(solc_usr_q_perm_set, 1)
                                    }
                                    {
                                        let solc_usr_q_perm_start := mul(solc_usr_q_perm_set, solc_usr_q_perm_chunk_len)
                                        let solc_usr_q_perm_end := add(solc_usr_q_perm_start, solc_usr_q_perm_chunk_len)
                                        if gt(solc_usr_q_perm_end, solc_usr_q_perm_num_cols)
                                        {
                                            solc_usr_q_perm_end := solc_usr_q_perm_num_cols
                                        }
                                        let solc_usr_q_perm_left := mload(add(solc_usr_q_perm_z_next, shl(5, solc_usr_q_perm_set)))
                                        let solc_usr_q_perm_right := mload(add(solc_usr_q_perm_z_cur, shl(5, solc_usr_q_perm_set)))
                                        let solc_usr_q_perm_delta_pow := mload(solc_usr_q_perm_delta_base_ptr)
                                        for {
                                            let solc_usr_q_perm_j := solc_usr_q_perm_start
                                        }
                                        lt(solc_usr_q_perm_j, solc_usr_q_perm_end)
                                        {
                                            solc_usr_q_perm_j := add(solc_usr_q_perm_j, 1)
                                        }
                                        {
                                            let solc_usr_q_perm_off := shl(5, solc_usr_q_perm_j)
                                            let solc_usr_q_perm_v := mload(add(solc_usr_q_perm_vals, solc_usr_q_perm_off))
                                            let solc_usr_q_perm_s := mload(add(solc_usr_q_perm_sigmas, solc_usr_q_perm_off))
                                            solc_usr_q_perm_left := mulmod(solc_usr_q_perm_left, addmod(addmod(solc_usr_q_perm_v, mulmod(mload(27040), solc_usr_q_perm_s, solc_usr_r), solc_usr_r), mload(27072), solc_usr_r), solc_usr_r)
                                            solc_usr_q_perm_right := mulmod(solc_usr_q_perm_right, addmod(addmod(solc_usr_q_perm_v, solc_usr_q_perm_delta_pow, solc_usr_r), mload(27072), solc_usr_r), solc_usr_r)
                                            solc_usr_q_perm_delta_pow := mulmod(solc_usr_q_perm_delta_pow, solc_usr_delta, solc_usr_r)
                                        }
                                        solc_usr_q_perm_eval := mulmod(addmod(1, sub(solc_usr_r, addmod(mload(27904), mload(27936), solc_usr_r)), solc_usr_r), addmod(solc_usr_q_perm_left, sub(solc_usr_r, solc_usr_q_perm_right), solc_usr_r), solc_usr_r)
                                        mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                        mstore(0xa300, addmod(mload(0xa300), solc_usr_q_perm_eval, solc_usr_r))
                                        mstore(solc_usr_q_perm_delta_base_ptr, mulmod(mload(solc_usr_q_perm_delta_base_ptr), solc_usr_q_perm_delta_chunk, solc_usr_r))
                                    }
                                }
                            }
                            case 0x1f {
                                solc_usr_q_top := 0
                                solc_usr_q_has_top := 0
                                solc_usr_q_sp := 0xa960
                                {
                                    let solc_usr_q_lookup_f := 0xa960
                                    let solc_usr_q_lookup_prefix := 0xa9e0
                                    let solc_usr_q_lookup_suffix := 0xaa60
                                    let solc_usr_q_lookup_l0 := mload(27968)
                                    let solc_usr_q_lookup_llast := mload(27904)
                                    let solc_usr_q_lookup_lblind := mload(27936)
                                    let solc_usr_q_lookup_lsum := addmod(solc_usr_q_lookup_l0, solc_usr_q_lookup_llast, solc_usr_r)
                                    let solc_usr_q_lookup_active := addmod(1, sub(solc_usr_r, addmod(solc_usr_q_lookup_llast, solc_usr_q_lookup_lblind, solc_usr_r)), solc_usr_r)
                                    let solc_usr_q_lookup_beta := mload(27040)
                                    let solc_usr_q_lookup_theta := mload(27008)
                                    {
                                        {
                                            let solc_usr_q_lookup_eval := mulmod(solc_usr_q_lookup_lsum, mload(0x90e0), solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                        {
                                            let solc_usr_f_10 := mload(0x8b60)
                                            let solc_usr_var0 := addmod(mulmod(0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_f_10, solc_usr_r)
                                            let solc_usr_var1 := mulmod(solc_usr_var0, solc_usr_q_lookup_theta, solc_usr_r)
                                            for {
                                                let solc_usr_q_lookup_shared_i := 0
                                            }
                                            lt(solc_usr_q_lookup_shared_i, 4)
                                            {
                                                solc_usr_q_lookup_shared_i := add(solc_usr_q_lookup_shared_i, 1)
                                            }
                                            {
                                                let solc_usr_q_lookup_shared_off := shl(5, solc_usr_q_lookup_shared_i)
                                                let solc_usr_q_lookup_shared_tail := mload(add(0x8540, solc_usr_q_lookup_shared_off))
                                                let solc_usr_q_lookup_shared_compressed := addmod(solc_usr_var1, solc_usr_q_lookup_shared_tail, solc_usr_r)
                                                mstore(add(solc_usr_q_lookup_f, solc_usr_q_lookup_shared_off), addmod(solc_usr_q_lookup_shared_compressed, solc_usr_q_lookup_beta, solc_usr_r))
                                            }
                                            let solc_usr_q_lookup_product := 1
                                            for { let solc_usr_q_lookup_prod_i := 0 }
                                            lt(solc_usr_q_lookup_prod_i, 4)
                                            {
                                                solc_usr_q_lookup_prod_i := add(solc_usr_q_lookup_prod_i, 1)
                                            }
                                            {
                                                solc_usr_q_lookup_product := mulmod(solc_usr_q_lookup_product, mload(add(solc_usr_q_lookup_f, shl(5, solc_usr_q_lookup_prod_i))), solc_usr_r)
                                            }
                                            mstore(solc_usr_q_lookup_prefix, 1)
                                            for { let solc_usr_q_lookup_pref_i := 1 }
                                            lt(solc_usr_q_lookup_pref_i, 4)
                                            {
                                                solc_usr_q_lookup_pref_i := add(solc_usr_q_lookup_pref_i, 1)
                                            }
                                            {
                                                let solc_usr_q_lookup_pref_prev := sub(solc_usr_q_lookup_pref_i, 1)
                                                mstore(add(solc_usr_q_lookup_prefix, shl(5, solc_usr_q_lookup_pref_i)), mulmod(mload(add(solc_usr_q_lookup_prefix, shl(5, solc_usr_q_lookup_pref_prev))), mload(add(solc_usr_q_lookup_f, shl(5, solc_usr_q_lookup_pref_prev))), solc_usr_r))
                                            }
                                            mstore(add(solc_usr_q_lookup_suffix, 0x60), 1)
                                            for {
                                                let solc_usr_q_lookup_suf_i := sub(4, 1)
                                            }
                                            gt(solc_usr_q_lookup_suf_i, 0)
                                            {
                                                solc_usr_q_lookup_suf_i := sub(solc_usr_q_lookup_suf_i, 1)
                                            }
                                            {
                                                let solc_usr_q_lookup_suf_prev := sub(solc_usr_q_lookup_suf_i, 1)
                                                mstore(add(solc_usr_q_lookup_suffix, shl(5, solc_usr_q_lookup_suf_prev)), mulmod(mload(add(solc_usr_q_lookup_suffix, shl(5, solc_usr_q_lookup_suf_i))), mload(add(solc_usr_q_lookup_f, shl(5, solc_usr_q_lookup_suf_i))), solc_usr_r))
                                            }
                                            let solc_usr_q_lookup_sum := 0
                                            for { let solc_usr_q_lookup_sum_i := 0 }
                                            lt(solc_usr_q_lookup_sum_i, 4)
                                            {
                                                solc_usr_q_lookup_sum_i := add(solc_usr_q_lookup_sum_i, 1)
                                            }
                                            {
                                                solc_usr_q_lookup_sum := addmod(solc_usr_q_lookup_sum, mulmod(mload(add(solc_usr_q_lookup_prefix, shl(5, solc_usr_q_lookup_sum_i))), mload(add(solc_usr_q_lookup_suffix, shl(5, solc_usr_q_lookup_sum_i))), solc_usr_r), solc_usr_r)
                                            }
                                            let solc_usr_q_lookup_eval := addmod(mulmod(mload(0x90c0), solc_usr_q_lookup_product, solc_usr_r), sub(solc_usr_r, solc_usr_q_lookup_sum), solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                        {
                                            let solc_usr_q_lookup_sum_h := mload(0x90c0)
                                            let solc_usr_f_17 := mload(0x8be0)
                                            let solc_usr_f_11 := mload(0x8b80)
                                            let solc_usr_var0 := addmod(mulmod(0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_f_11, solc_usr_r)
                                            let solc_usr_f_12 := mload(0x8ba0)
                                            let solc_usr_var1 := addmod(mulmod(solc_usr_var0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_f_12, solc_usr_r)
                                            let solc_usr_q_lookup_s_sum_h := mulmod(solc_usr_f_17, solc_usr_q_lookup_sum_h, solc_usr_r)
                                            let solc_usr_q_lookup_diff := addmod(mload(0x9100), sub(solc_usr_r, addmod(mload(0x90e0), solc_usr_q_lookup_s_sum_h, solc_usr_r)), solc_usr_r)
                                            let solc_usr_q_lookup_t_beta := addmod(solc_usr_var1, solc_usr_q_lookup_beta, solc_usr_r)
                                            let solc_usr_q_lookup_core := addmod(mulmod(solc_usr_q_lookup_diff, solc_usr_q_lookup_t_beta, solc_usr_r), mload(0x90a0), solc_usr_r)
                                            let solc_usr_q_lookup_eval := mulmod(solc_usr_q_lookup_active, solc_usr_q_lookup_core, solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                    }
                                    {
                                        {
                                            let solc_usr_q_lookup_eval := mulmod(solc_usr_q_lookup_lsum, mload(0x9160), solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                        {
                                            let solc_usr_a_14 := mload(0x8a00)
                                            let solc_usr_var0 := addmod(mulmod(0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_14, solc_usr_r)
                                            let solc_usr_a_0 := mload(0x8520)
                                            let solc_usr_var1 := addmod(mulmod(solc_usr_var0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_0, solc_usr_r)
                                            let solc_usr_a_1 := mload(0x8540)
                                            let solc_usr_var2 := addmod(mulmod(solc_usr_var1, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_1, solc_usr_r)
                                            let solc_usr_a_2 := mload(0x8560)
                                            let solc_usr_var3 := addmod(mulmod(solc_usr_var2, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_2, solc_usr_r)
                                            let solc_usr_a_3 := mload(0x8580)
                                            let solc_usr_var4 := addmod(mulmod(solc_usr_var3, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_3, solc_usr_r)
                                            let solc_usr_a_4 := mload(0x85a0)
                                            let solc_usr_var5 := addmod(mulmod(solc_usr_var4, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_4, solc_usr_r)
                                            let solc_usr_a_5 := mload(0x8620)
                                            let solc_usr_var6 := addmod(mulmod(solc_usr_var5, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_5, solc_usr_r)
                                            let solc_usr_a_6 := mload(0x8640)
                                            let solc_usr_var7 := addmod(mulmod(solc_usr_var6, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_6, solc_usr_r)
                                            let solc_usr_a_7 := mload(0x8660)
                                            let solc_usr_var8 := addmod(mulmod(solc_usr_var7, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_7, solc_usr_r)
                                            let solc_usr_a_8 := mload(0x8680)
                                            let solc_usr_var9 := addmod(mulmod(solc_usr_var8, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_8, solc_usr_r)
                                            let solc_usr_a_9 := mload(0x86a0)
                                            let solc_usr_var10 := addmod(mulmod(solc_usr_var9, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_9, solc_usr_r)
                                            let solc_usr_a_10 := mload(0x86c0)
                                            let solc_usr_var11 := addmod(mulmod(solc_usr_var10, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_10, solc_usr_r)
                                            let solc_usr_a_11 := mload(0x86e0)
                                            let solc_usr_var12 := addmod(mulmod(solc_usr_var11, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_11, solc_usr_r)
                                            let solc_usr_a_12 := mload(0x8700)
                                            let solc_usr_var13 := addmod(mulmod(solc_usr_var12, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_12, solc_usr_r)
                                            let solc_usr_a_13 := mload(0x8720)
                                            let solc_usr_var14 := addmod(mulmod(solc_usr_var13, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_a_13, solc_usr_r)
                                            let solc_usr_f_13 := mload(0x8bc0)
                                            let solc_usr_var15 := addmod(mulmod(solc_usr_var14, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_f_13, solc_usr_r)
                                            let solc_usr_q_lookup_eval := addmod(mulmod(mload(0x9140), addmod(solc_usr_var15, solc_usr_q_lookup_beta, solc_usr_r), solc_usr_r), sub(solc_usr_r, 1), solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                        {
                                            let solc_usr_q_lookup_sum_h := mload(0x9140)
                                            let solc_usr_var0 := 0x1
                                            let solc_usr_f_24 := mload(0x8c00)
                                            let solc_usr_var1 := addmod(0, sub(solc_usr_r, solc_usr_f_24), solc_usr_r)
                                            let solc_usr_var2 := addmod(solc_usr_var0, solc_usr_var1, solc_usr_r)
                                            let solc_usr_a_14 := mload(0x8a00)
                                            let solc_usr_var3 := mulmod(solc_usr_var2, solc_usr_a_14, solc_usr_r)
                                            let solc_usr_var4 := addmod(mulmod(0, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var3, solc_usr_r)
                                            let solc_usr_a_0 := mload(0x8520)
                                            let solc_usr_var5 := mulmod(solc_usr_var2, solc_usr_a_0, solc_usr_r)
                                            let solc_usr_var6 := addmod(mulmod(solc_usr_var4, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var5, solc_usr_r)
                                            let solc_usr_a_1 := mload(0x8540)
                                            let solc_usr_var7 := mulmod(solc_usr_var2, solc_usr_a_1, solc_usr_r)
                                            let solc_usr_var8 := addmod(mulmod(solc_usr_var6, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var7, solc_usr_r)
                                            let solc_usr_a_2 := mload(0x8560)
                                            let solc_usr_var9 := mulmod(solc_usr_var2, solc_usr_a_2, solc_usr_r)
                                            let solc_usr_var10 := addmod(mulmod(solc_usr_var8, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var9, solc_usr_r)
                                            let solc_usr_a_3 := mload(0x8580)
                                            let solc_usr_var11 := mulmod(solc_usr_var2, solc_usr_a_3, solc_usr_r)
                                            let solc_usr_var12 := addmod(mulmod(solc_usr_var10, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var11, solc_usr_r)
                                            let solc_usr_a_4 := mload(0x85a0)
                                            let solc_usr_var13 := mulmod(solc_usr_var2, solc_usr_a_4, solc_usr_r)
                                            let solc_usr_var14 := addmod(mulmod(solc_usr_var12, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var13, solc_usr_r)
                                            let solc_usr_a_5 := mload(0x8620)
                                            let solc_usr_var15 := mulmod(solc_usr_var2, solc_usr_a_5, solc_usr_r)
                                            let solc_usr_var16 := addmod(mulmod(solc_usr_var14, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var15, solc_usr_r)
                                            let solc_usr_a_6 := mload(0x8640)
                                            let solc_usr_var17 := mulmod(solc_usr_var2, solc_usr_a_6, solc_usr_r)
                                            let solc_usr_var18 := addmod(mulmod(solc_usr_var16, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var17, solc_usr_r)
                                            let solc_usr_a_7 := mload(0x8660)
                                            let solc_usr_var19 := mulmod(solc_usr_var2, solc_usr_a_7, solc_usr_r)
                                            let solc_usr_var20 := addmod(mulmod(solc_usr_var18, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var19, solc_usr_r)
                                            let solc_usr_a_8 := mload(0x8680)
                                            let solc_usr_var21 := mulmod(solc_usr_var2, solc_usr_a_8, solc_usr_r)
                                            let solc_usr_var22 := addmod(mulmod(solc_usr_var20, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var21, solc_usr_r)
                                            let solc_usr_a_9 := mload(0x86a0)
                                            let solc_usr_var23 := mulmod(solc_usr_var2, solc_usr_a_9, solc_usr_r)
                                            let solc_usr_var24 := addmod(mulmod(solc_usr_var22, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var23, solc_usr_r)
                                            let solc_usr_a_10 := mload(0x86c0)
                                            let solc_usr_var25 := mulmod(solc_usr_var2, solc_usr_a_10, solc_usr_r)
                                            let solc_usr_var26 := addmod(mulmod(solc_usr_var24, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var25, solc_usr_r)
                                            let solc_usr_a_11 := mload(0x86e0)
                                            let solc_usr_var27 := mulmod(solc_usr_var2, solc_usr_a_11, solc_usr_r)
                                            let solc_usr_var28 := addmod(mulmod(solc_usr_var26, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var27, solc_usr_r)
                                            let solc_usr_a_12 := mload(0x8700)
                                            let solc_usr_var29 := mulmod(solc_usr_var2, solc_usr_a_12, solc_usr_r)
                                            let solc_usr_var30 := addmod(mulmod(solc_usr_var28, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var29, solc_usr_r)
                                            let solc_usr_a_13 := mload(0x8720)
                                            let solc_usr_var31 := mulmod(solc_usr_var2, solc_usr_a_13, solc_usr_r)
                                            let solc_usr_var32 := addmod(mulmod(solc_usr_var30, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var31, solc_usr_r)
                                            let solc_usr_f_13 := mload(0x8bc0)
                                            let solc_usr_var33 := mulmod(solc_usr_var2, solc_usr_f_13, solc_usr_r)
                                            let solc_usr_var34 := addmod(mulmod(solc_usr_var32, solc_usr_q_lookup_theta, solc_usr_r), solc_usr_var33, solc_usr_r)
                                            let solc_usr_q_lookup_s_sum_h := mulmod(solc_usr_var0, solc_usr_q_lookup_sum_h, solc_usr_r)
                                            let solc_usr_q_lookup_diff := addmod(mload(0x9180), sub(solc_usr_r, addmod(mload(0x9160), solc_usr_q_lookup_s_sum_h, solc_usr_r)), solc_usr_r)
                                            let solc_usr_q_lookup_t_beta := addmod(solc_usr_var34, solc_usr_q_lookup_beta, solc_usr_r)
                                            let solc_usr_q_lookup_core := addmod(mulmod(solc_usr_q_lookup_diff, solc_usr_q_lookup_t_beta, solc_usr_r), mload(0x9120), solc_usr_r)
                                            let solc_usr_q_lookup_eval := mulmod(solc_usr_q_lookup_active, solc_usr_q_lookup_core, solc_usr_r)
                                            mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                            mstore(0xa300, addmod(mload(0xa300), solc_usr_q_lookup_eval, solc_usr_r))
                                        }
                                    }
                                }
                            }
                            case 0x1b {
                                let solc_usr_q_native_idx := shr(240, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 2)
                                solc_usr_q_top := 0
                                solc_usr_q_has_top := 0
                                solc_usr_q_sp := 0xa960
                                switch solc_usr_q_native_idx
                                case 0 {
                                    {
                                        let solc_usr_var0 := 0x1
                                        let solc_usr_a_0 := mload(0x8520)
                                        let solc_usr_a_0_next_1 := mload(0x85c0)
                                        let solc_usr_var1 := mulmod(solc_usr_a_0, solc_usr_a_0_next_1, solc_usr_r)
                                        let solc_usr_var2 := 0x100000000000000
                                        let solc_usr_a_1_next_1 := mload(0x85e0)
                                        let solc_usr_var3 := mulmod(solc_usr_a_0, solc_usr_a_1_next_1, solc_usr_r)
                                        let solc_usr_var4 := mulmod(solc_usr_var2, solc_usr_var3, solc_usr_r)
                                        let solc_usr_var5 := addmod(solc_usr_var1, solc_usr_var4, solc_usr_r)
                                        let solc_usr_var6 := 0x10000000000000000000000000000
                                        let solc_usr_a_2_next_1 := mload(0x8600)
                                        let solc_usr_var7 := mulmod(solc_usr_a_0, solc_usr_a_2_next_1, solc_usr_r)
                                        let solc_usr_var8 := mulmod(solc_usr_var6, solc_usr_var7, solc_usr_r)
                                        let solc_usr_var9 := addmod(solc_usr_var5, solc_usr_var8, solc_usr_r)
                                        let solc_usr_a_1 := mload(0x8540)
                                        let solc_usr_var10 := mulmod(solc_usr_a_1, solc_usr_a_0_next_1, solc_usr_r)
                                        let solc_usr_var11 := mulmod(solc_usr_var2, solc_usr_var10, solc_usr_r)
                                        let solc_usr_var12 := addmod(solc_usr_var9, solc_usr_var11, solc_usr_r)
                                        let solc_usr_var13 := mulmod(solc_usr_a_1, solc_usr_a_1_next_1, solc_usr_r)
                                        let solc_usr_var14 := mulmod(solc_usr_var6, solc_usr_var13, solc_usr_r)
                                        let solc_usr_var15 := addmod(solc_usr_var12, solc_usr_var14, solc_usr_r)
                                        let solc_usr_var16 := 0x3212e00cde6d2002b119d800000347fcb8
                                        let solc_usr_a_6_next_1 := mload(0x87a0)
                                        let solc_usr_var17 := mulmod(solc_usr_a_1, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var18 := mulmod(solc_usr_var16, solc_usr_var17, solc_usr_r)
                                        let solc_usr_var19 := addmod(solc_usr_var15, solc_usr_var18, solc_usr_r)
                                        let solc_usr_a_2 := mload(0x8560)
                                        let solc_usr_var20 := mulmod(solc_usr_a_2, solc_usr_a_0_next_1, solc_usr_r)
                                        let solc_usr_var21 := mulmod(solc_usr_var6, solc_usr_var20, solc_usr_r)
                                        let solc_usr_var22 := addmod(solc_usr_var19, solc_usr_var21, solc_usr_r)
                                        let solc_usr_a_5_next_1 := mload(0x8780)
                                        let solc_usr_var23 := mulmod(solc_usr_a_2, solc_usr_a_5_next_1, solc_usr_r)
                                        let solc_usr_var24 := mulmod(solc_usr_var16, solc_usr_var23, solc_usr_r)
                                        let solc_usr_var25 := addmod(solc_usr_var22, solc_usr_var24, solc_usr_r)
                                        let solc_usr_var26 := 0x297784894e27525bc342b7fde37dba9366
                                        let solc_usr_var27 := mulmod(solc_usr_a_2, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var28 := mulmod(solc_usr_var26, solc_usr_var27, solc_usr_r)
                                        let solc_usr_var29 := addmod(solc_usr_var25, solc_usr_var28, solc_usr_r)
                                        let solc_usr_a_3 := mload(0x8580)
                                        let solc_usr_a_4_next_1 := mload(0x8760)
                                        let solc_usr_var30 := mulmod(solc_usr_a_3, solc_usr_a_4_next_1, solc_usr_r)
                                        let solc_usr_var31 := mulmod(solc_usr_var16, solc_usr_var30, solc_usr_r)
                                        let solc_usr_var32 := addmod(solc_usr_var29, solc_usr_var31, solc_usr_r)
                                        let solc_usr_var33 := mulmod(solc_usr_a_3, solc_usr_a_5_next_1, solc_usr_r)
                                        let solc_usr_var34 := mulmod(solc_usr_var26, solc_usr_var33, solc_usr_r)
                                        let solc_usr_var35 := addmod(solc_usr_var32, solc_usr_var34, solc_usr_r)
                                        let solc_usr_var36 := 0x340f2ebe380a0f5eff4360543988a61dc2
                                        let solc_usr_var37 := mulmod(solc_usr_a_3, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var38 := mulmod(solc_usr_var36, solc_usr_var37, solc_usr_r)
                                        let solc_usr_var39 := addmod(solc_usr_var35, solc_usr_var38, solc_usr_r)
                                        let solc_usr_a_4 := mload(0x85a0)
                                        let solc_usr_a_3_next_1 := mload(0x8740)
                                        let solc_usr_var40 := mulmod(solc_usr_a_4, solc_usr_a_3_next_1, solc_usr_r)
                                        let solc_usr_var41 := mulmod(solc_usr_var16, solc_usr_var40, solc_usr_r)
                                        let solc_usr_var42 := addmod(solc_usr_var39, solc_usr_var41, solc_usr_r)
                                        let solc_usr_var43 := mulmod(solc_usr_a_4, solc_usr_a_4_next_1, solc_usr_r)
                                        let solc_usr_var44 := mulmod(solc_usr_var26, solc_usr_var43, solc_usr_r)
                                        let solc_usr_var45 := addmod(solc_usr_var42, solc_usr_var44, solc_usr_r)
                                        let solc_usr_var46 := mulmod(solc_usr_a_4, solc_usr_a_5_next_1, solc_usr_r)
                                        let solc_usr_var47 := mulmod(solc_usr_var36, solc_usr_var46, solc_usr_r)
                                        let solc_usr_var48 := addmod(solc_usr_var45, solc_usr_var47, solc_usr_r)
                                        let solc_usr_var49 := 0x13af65741744bd7bb2c6872df2b800320
                                        let solc_usr_var50 := mulmod(solc_usr_a_4, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var51 := mulmod(solc_usr_var49, solc_usr_var50, solc_usr_r)
                                        let solc_usr_var52 := addmod(solc_usr_var48, solc_usr_var51, solc_usr_r)
                                        let solc_usr_a_5 := mload(0x8620)
                                        let solc_usr_var53 := mulmod(solc_usr_a_5, solc_usr_a_2_next_1, solc_usr_r)
                                        let solc_usr_var54 := mulmod(solc_usr_var16, solc_usr_var53, solc_usr_r)
                                        let solc_usr_var55 := addmod(solc_usr_var52, solc_usr_var54, solc_usr_r)
                                        let solc_usr_var56 := mulmod(solc_usr_a_5, solc_usr_a_3_next_1, solc_usr_r)
                                        let solc_usr_var57 := mulmod(solc_usr_var26, solc_usr_var56, solc_usr_r)
                                        let solc_usr_var58 := addmod(solc_usr_var55, solc_usr_var57, solc_usr_r)
                                        let solc_usr_var59 := mulmod(solc_usr_a_5, solc_usr_a_4_next_1, solc_usr_r)
                                        let solc_usr_var60 := mulmod(solc_usr_var36, solc_usr_var59, solc_usr_r)
                                        let solc_usr_var61 := addmod(solc_usr_var58, solc_usr_var60, solc_usr_r)
                                        let solc_usr_var62 := mulmod(solc_usr_a_5, solc_usr_a_5_next_1, solc_usr_r)
                                        let solc_usr_var63 := mulmod(solc_usr_var49, solc_usr_var62, solc_usr_r)
                                        let solc_usr_var64 := addmod(solc_usr_var61, solc_usr_var63, solc_usr_r)
                                        let solc_usr_var65 := 0x2cb9b546d20373eaf85e8f53db883cb548
                                        let solc_usr_var66 := mulmod(solc_usr_a_5, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var67 := mulmod(solc_usr_var65, solc_usr_var66, solc_usr_r)
                                        let solc_usr_var68 := addmod(solc_usr_var64, solc_usr_var67, solc_usr_r)
                                        let solc_usr_a_6 := mload(0x8640)
                                        let solc_usr_var69 := mulmod(solc_usr_a_6, solc_usr_a_1_next_1, solc_usr_r)
                                        let solc_usr_var70 := mulmod(solc_usr_var16, solc_usr_var69, solc_usr_r)
                                        let solc_usr_var71 := addmod(solc_usr_var68, solc_usr_var70, solc_usr_r)
                                        let solc_usr_var72 := mulmod(solc_usr_a_6, solc_usr_a_2_next_1, solc_usr_r)
                                        let solc_usr_var73 := mulmod(solc_usr_var26, solc_usr_var72, solc_usr_r)
                                        let solc_usr_var74 := addmod(solc_usr_var71, solc_usr_var73, solc_usr_r)
                                        let solc_usr_var75 := mulmod(solc_usr_a_6, solc_usr_a_3_next_1, solc_usr_r)
                                        let solc_usr_var76 := mulmod(solc_usr_var36, solc_usr_var75, solc_usr_r)
                                        let solc_usr_var77 := addmod(solc_usr_var74, solc_usr_var76, solc_usr_r)
                                        let solc_usr_var78 := mulmod(solc_usr_a_6, solc_usr_a_4_next_1, solc_usr_r)
                                        let solc_usr_var79 := mulmod(solc_usr_var49, solc_usr_var78, solc_usr_r)
                                        let solc_usr_var80 := addmod(solc_usr_var77, solc_usr_var79, solc_usr_r)
                                        let solc_usr_var81 := mulmod(solc_usr_a_6, solc_usr_a_5_next_1, solc_usr_r)
                                        let solc_usr_var82 := mulmod(solc_usr_var65, solc_usr_var81, solc_usr_r)
                                        let solc_usr_var83 := addmod(solc_usr_var80, solc_usr_var82, solc_usr_r)
                                        let solc_usr_var84 := 0xc8557e86f90d0d89eed6eb5349a0f8820
                                        let solc_usr_var85 := mulmod(solc_usr_a_6, solc_usr_a_6_next_1, solc_usr_r)
                                        let solc_usr_var86 := mulmod(solc_usr_var84, solc_usr_var85, solc_usr_r)
                                        let solc_usr_var87 := addmod(solc_usr_var83, solc_usr_var86, solc_usr_r)
                                        let solc_usr_var88 := mulmod(solc_usr_var2, solc_usr_a_1, solc_usr_r)
                                        let solc_usr_var89 := addmod(solc_usr_a_0, solc_usr_var88, solc_usr_r)
                                        let solc_usr_var90 := mulmod(solc_usr_var6, solc_usr_a_2, solc_usr_r)
                                        let solc_usr_var91 := addmod(solc_usr_var89, solc_usr_var90, solc_usr_r)
                                        let solc_usr_var92 := addmod(solc_usr_var87, solc_usr_var91, solc_usr_r)
                                        let solc_usr_var93 := mulmod(solc_usr_var2, solc_usr_a_1_next_1, solc_usr_r)
                                        let solc_usr_var94 := addmod(solc_usr_a_0_next_1, solc_usr_var93, solc_usr_r)
                                        let solc_usr_var95 := mulmod(solc_usr_var6, solc_usr_a_2_next_1, solc_usr_r)
                                        let solc_usr_var96 := addmod(solc_usr_var94, solc_usr_var95, solc_usr_r)
                                        let solc_usr_var97 := addmod(solc_usr_var92, solc_usr_var96, solc_usr_r)
                                        let solc_usr_a_7 := mload(0x8660)
                                        let solc_usr_a_8 := mload(0x8680)
                                        let solc_usr_var98 := mulmod(solc_usr_var2, solc_usr_a_8, solc_usr_r)
                                        let solc_usr_var99 := addmod(solc_usr_a_7, solc_usr_var98, solc_usr_r)
                                        let solc_usr_a_9 := mload(0x86a0)
                                        let solc_usr_var100 := mulmod(solc_usr_var6, solc_usr_a_9, solc_usr_r)
                                        let solc_usr_var101 := addmod(solc_usr_var99, solc_usr_var100, solc_usr_r)
                                        let solc_usr_var102 := addmod(0, sub(solc_usr_r, solc_usr_var101), solc_usr_r)
                                        let solc_usr_var103 := addmod(solc_usr_var97, solc_usr_var102, solc_usr_r)
                                        let solc_usr_a_7_next_1 := mload(0x87c0)
                                        let solc_usr_var104 := 0x241eabfffeb153ffffb9feffffffffaaab
                                        let solc_usr_var105 := mulmod(solc_usr_a_7_next_1, solc_usr_var104, solc_usr_r)
                                        let solc_usr_var106 := addmod(0, sub(solc_usr_r, solc_usr_var105), solc_usr_r)
                                        let solc_usr_var107 := addmod(solc_usr_var103, solc_usr_var106, solc_usr_r)
                                        let solc_usr_var108 := addmod(0, sub(solc_usr_r, solc_usr_var16), solc_usr_r)
                                        let solc_usr_var109 := addmod(solc_usr_var107, solc_usr_var108, solc_usr_r)
                                        let solc_usr_a_8_next_1 := mload(0x87e0)
                                        let solc_usr_var110 := 0x73eda753299d7d483339d80809a1d80553b9202d7ffe85d4800008bb20000001
                                        let solc_usr_var111 := addmod(solc_usr_a_8_next_1, solc_usr_var110, solc_usr_r)
                                        let solc_usr_var112 := 0x4000000000000000000000000000000000
                                        let solc_usr_var113 := mulmod(solc_usr_var111, solc_usr_var112, solc_usr_r)
                                        let solc_usr_var114 := addmod(0, sub(solc_usr_r, solc_usr_var113), solc_usr_r)
                                        let solc_usr_var115 := addmod(solc_usr_var109, solc_usr_var114, solc_usr_r)
                                        let solc_usr_var116 := mulmod(solc_usr_var0, solc_usr_var115, solc_usr_r)
                                        mstore(0xa960, solc_usr_var116)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    {
                                        let solc_usr_q_selector_ptr := add(41408, 0x60)
                                        let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                                        mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                                    }
                                }
                                case 1 {
                                    {
                                        let solc_usr_var0 := 0x1
                                        let solc_usr_a_0 := mload(0x8520)
                                        let solc_usr_var1 := 0x10000000000000000000000000000
                                        let solc_usr_var2 := addmod(solc_usr_a_0, solc_usr_var1, solc_usr_r)
                                        let solc_usr_var3 := 0x100000000000000
                                        let solc_usr_a_1 := mload(0x8540)
                                        let solc_usr_var4 := addmod(solc_usr_a_1, solc_usr_var1, solc_usr_r)
                                        let solc_usr_var5 := mulmod(solc_usr_var3, solc_usr_var4, solc_usr_r)
                                        let solc_usr_var6 := addmod(solc_usr_var2, solc_usr_var5, solc_usr_r)
                                        let solc_usr_a_2 := mload(0x8560)
                                        let solc_usr_var7 := addmod(solc_usr_a_2, solc_usr_var1, solc_usr_r)
                                        let solc_usr_var8 := mulmod(solc_usr_var1, solc_usr_var7, solc_usr_r)
                                        let solc_usr_var9 := addmod(solc_usr_var6, solc_usr_var8, solc_usr_r)
                                        let solc_usr_a_7 := mload(0x8660)
                                        let solc_usr_a_8 := mload(0x8680)
                                        let solc_usr_var10 := mulmod(solc_usr_var3, solc_usr_a_8, solc_usr_r)
                                        let solc_usr_var11 := addmod(solc_usr_a_7, solc_usr_var10, solc_usr_r)
                                        let solc_usr_a_9 := mload(0x86a0)
                                        let solc_usr_var12 := mulmod(solc_usr_var1, solc_usr_a_9, solc_usr_r)
                                        let solc_usr_var13 := addmod(solc_usr_var11, solc_usr_var12, solc_usr_r)
                                        let solc_usr_var14 := addmod(0, sub(solc_usr_r, solc_usr_var13), solc_usr_r)
                                        let solc_usr_var15 := addmod(solc_usr_var9, solc_usr_var14, solc_usr_r)
                                        let solc_usr_var16 := addmod(0, sub(solc_usr_r, solc_usr_var1), solc_usr_r)
                                        let solc_usr_var17 := addmod(solc_usr_var15, solc_usr_var16, solc_usr_r)
                                        let solc_usr_a_7_next_1 := mload(0x87c0)
                                        let solc_usr_var18 := 0x241eabfffeb153ffffb9feffffffffaaab
                                        let solc_usr_var19 := mulmod(solc_usr_a_7_next_1, solc_usr_var18, solc_usr_r)
                                        let solc_usr_var20 := addmod(0, sub(solc_usr_r, solc_usr_var19), solc_usr_r)
                                        let solc_usr_var21 := addmod(solc_usr_var17, solc_usr_var20, solc_usr_r)
                                        let solc_usr_var22 := 0xd9d44a30b019261257667fde3844a8cd6
                                        let solc_usr_var23 := addmod(0, sub(solc_usr_r, solc_usr_var22), solc_usr_r)
                                        let solc_usr_var24 := addmod(solc_usr_var21, solc_usr_var23, solc_usr_r)
                                        let solc_usr_a_8_next_1 := mload(0x87e0)
                                        let solc_usr_var25 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5b6e855000003ab00002
                                        let solc_usr_var26 := addmod(solc_usr_a_8_next_1, solc_usr_var25, solc_usr_r)
                                        let solc_usr_var27 := 0x4000000000000000000000000000000000
                                        let solc_usr_var28 := mulmod(solc_usr_var26, solc_usr_var27, solc_usr_r)
                                        let solc_usr_var29 := addmod(0, sub(solc_usr_r, solc_usr_var28), solc_usr_r)
                                        let solc_usr_var30 := addmod(solc_usr_var24, solc_usr_var29, solc_usr_r)
                                        let solc_usr_var31 := mulmod(solc_usr_var0, solc_usr_var30, solc_usr_r)
                                        mstore(0xa960, solc_usr_var31)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    {
                                        let solc_usr_q_selector_ptr := add(41408, 0x80)
                                        let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                                        mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                                    }
                                }
                                case 2 {
                                    {
                                        let solc_usr_var0 := 0x1
                                        let solc_usr_f_0 := mload(0x8ae0)
                                        let solc_usr_a_0_next_1 := mload(0x85c0)
                                        let solc_usr_var1 := addmod(0, sub(solc_usr_r, solc_usr_a_0_next_1), solc_usr_r)
                                        let solc_usr_var2 := addmod(solc_usr_f_0, solc_usr_var1, solc_usr_r)
                                        let solc_usr_var3 := 0x1b8114c381b922fd5d6d241210e2d8a68ad5744053ba9e776118de4107b51ace
                                        let solc_usr_a_0 := mload(0x8520)
                                        let solc_usr_var4 := mulmod(solc_usr_a_0, solc_usr_a_0, solc_usr_r)
                                        let solc_usr_a_3 := mload(0x8580)
                                        let solc_usr_var5 := mulmod(solc_usr_var4, solc_usr_a_3, solc_usr_r)
                                        let solc_usr_var6 := mulmod(solc_usr_var3, solc_usr_var5, solc_usr_r)
                                        let solc_usr_var7 := addmod(solc_usr_var2, solc_usr_var6, solc_usr_r)
                                        let solc_usr_var8 := 0x3df32e4cc4cb2ed20e5d21899cf5331775990ccaec4c09b4e3717213fcc0d763
                                        let solc_usr_a_1 := mload(0x8540)
                                        let solc_usr_var9 := mulmod(solc_usr_a_1, solc_usr_a_1, solc_usr_r)
                                        let solc_usr_a_4 := mload(0x85a0)
                                        let solc_usr_var10 := mulmod(solc_usr_var9, solc_usr_a_4, solc_usr_r)
                                        let solc_usr_var11 := mulmod(solc_usr_var8, solc_usr_var10, solc_usr_r)
                                        let solc_usr_var12 := addmod(solc_usr_var7, solc_usr_var11, solc_usr_r)
                                        let solc_usr_var13 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                                        let solc_usr_a_2 := mload(0x8560)
                                        let solc_usr_var14 := mulmod(solc_usr_a_2, solc_usr_a_2, solc_usr_r)
                                        let solc_usr_a_5 := mload(0x8620)
                                        let solc_usr_var15 := mulmod(solc_usr_var14, solc_usr_a_5, solc_usr_r)
                                        let solc_usr_var16 := mulmod(solc_usr_var13, solc_usr_var15, solc_usr_r)
                                        let solc_usr_var17 := addmod(solc_usr_var12, solc_usr_var16, solc_usr_r)
                                        let solc_usr_var18 := mulmod(solc_usr_var0, solc_usr_var17, solc_usr_r)
                                        mstore(0xa960, solc_usr_var18)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    {
                                        let solc_usr_q_selector_ptr := add(41408, 0x120)
                                        let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                                        solc_usr_q_selector_acc := mulmod(solc_usr_q_selector_acc, mload(add(0xa340, 0x20)), solc_usr_r)
                                        mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                                    }
                                }
                                case 3 {
                                    {
                                        let solc_usr_var0 := 0x1
                                        let solc_usr_f_1 := mload(0x8b00)
                                        let solc_usr_a_1_next_1 := mload(0x85e0)
                                        let solc_usr_var1 := addmod(0, sub(solc_usr_r, solc_usr_a_1_next_1), solc_usr_r)
                                        let solc_usr_var2 := addmod(solc_usr_f_1, solc_usr_var1, solc_usr_r)
                                        let solc_usr_var3 := 0x404d21073985d14e432a4ad76d3fae06ca74314b950fe7b1d7f501cd31a8b374
                                        let solc_usr_a_0 := mload(0x8520)
                                        let solc_usr_var4 := mulmod(solc_usr_a_0, solc_usr_a_0, solc_usr_r)
                                        let solc_usr_a_3 := mload(0x8580)
                                        let solc_usr_var5 := mulmod(solc_usr_var4, solc_usr_a_3, solc_usr_r)
                                        let solc_usr_var6 := mulmod(solc_usr_var3, solc_usr_var5, solc_usr_r)
                                        let solc_usr_var7 := addmod(solc_usr_var2, solc_usr_var6, solc_usr_r)
                                        let solc_usr_var8 := 0xb2cc8704264c6bd81bc620e9e524d4b73e9b2317679422ff7fa1603955649f1
                                        let solc_usr_a_1 := mload(0x8540)
                                        let solc_usr_var9 := mulmod(solc_usr_a_1, solc_usr_a_1, solc_usr_r)
                                        let solc_usr_a_4 := mload(0x85a0)
                                        let solc_usr_var10 := mulmod(solc_usr_var9, solc_usr_a_4, solc_usr_r)
                                        let solc_usr_var11 := mulmod(solc_usr_var8, solc_usr_var10, solc_usr_r)
                                        let solc_usr_var12 := addmod(solc_usr_var7, solc_usr_var11, solc_usr_r)
                                        let solc_usr_var13 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                                        let solc_usr_a_2 := mload(0x8560)
                                        let solc_usr_var14 := mulmod(solc_usr_a_2, solc_usr_a_2, solc_usr_r)
                                        let solc_usr_a_5 := mload(0x8620)
                                        let solc_usr_var15 := mulmod(solc_usr_var14, solc_usr_a_5, solc_usr_r)
                                        let solc_usr_var16 := mulmod(solc_usr_var13, solc_usr_var15, solc_usr_r)
                                        let solc_usr_var17 := addmod(solc_usr_var12, solc_usr_var16, solc_usr_r)
                                        let solc_usr_var18 := mulmod(solc_usr_var0, solc_usr_var17, solc_usr_r)
                                        mstore(0xa960, solc_usr_var18)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                    {
                                        let solc_usr_q_selector_ptr := add(41408, 0x120)
                                        let solc_usr_q_selector_acc := mload(solc_usr_q_selector_ptr)
                                        solc_usr_q_selector_acc := mulmod(solc_usr_q_selector_acc, mload(add(0xa340, 0x20)), solc_usr_r)
                                        mstore(solc_usr_q_selector_ptr, addmod(solc_usr_q_selector_acc, mload(0xa960), solc_usr_r))
                                    }
                                }
                                default { revert(0, 0) }
                            }
                            case 0x0b {
                                let solc_usr_q_selector_payload := shr(232, mload(solc_usr_q_pc))
                                solc_usr_q_pc := add(solc_usr_q_pc, 3)
                                let solc_usr_q_sel_idx := shr(16, solc_usr_q_selector_payload)
                                let solc_usr_q_sel_gap := and(solc_usr_q_selector_payload, 0xffff)
                                let solc_usr_q_eval := solc_usr_q_top
                                solc_usr_q_has_top := 0
                                mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                let solc_usr_q_target_ptr := add(41408, shl(5, solc_usr_q_sel_idx))
                                let solc_usr_q_sel_acc := mload(solc_usr_q_target_ptr)
                                if solc_usr_q_sel_gap
                                {
                                    solc_usr_q_sel_acc := mulmod(solc_usr_q_sel_acc, mload(add(0xa340, shl(5, solc_usr_q_sel_gap))), solc_usr_r)
                                }
                                mstore(solc_usr_q_target_ptr, addmod(solc_usr_q_sel_acc, solc_usr_q_eval, solc_usr_r))
                            }
                            default { revert(0, 0) }
                        }
                        if iszero(eq(solc_usr_q_pc, solc_usr_q_end)) { revert(0, 0) }
                        if solc_usr_q_has_top { revert(0, 0) }
                        {
                            let solc_usr_q_trash_tau := mload(27104)
                            {
                                let solc_usr_f_0 := mload(0x8ae0)
                                let solc_usr_a_0_next_1 := mload(0x85c0)
                                let solc_usr_var0 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
                                let solc_usr_var1 := mulmod(solc_usr_a_0_next_1, solc_usr_var0, solc_usr_r)
                                let solc_usr_var2 := addmod(solc_usr_f_0, solc_usr_var1, solc_usr_r)
                                let solc_usr_var3 := 0x590ba402032e82eb1f660ef09796c5686345a5054ed96dae8e2d233633788771
                                let solc_usr_a_0 := mload(0x8520)
                                let solc_usr_var4 := mulmod(solc_usr_var3, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var5 := addmod(solc_usr_var2, solc_usr_var4, solc_usr_r)
                                let solc_usr_var6 := 0x52f789e4afc3801f7411102ee2f47cc5954a744e71cac98e75ea962a55a0a76f
                                let solc_usr_a_1 := mload(0x8540)
                                let solc_usr_var7 := mulmod(solc_usr_var6, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var8 := addmod(solc_usr_var5, solc_usr_var7, solc_usr_r)
                                let solc_usr_var9 := 0x3509dd2fe3aac0080783557fec090fb1cb4b2b0901253c55282024331d1fe1a8
                                let solc_usr_a_2 := mload(0x8560)
                                let solc_usr_var10 := solc_usr_q_pow5(solc_usr_a_2)
                                let solc_usr_var11 := mulmod(solc_usr_var9, solc_usr_var10, solc_usr_r)
                                let solc_usr_var12 := addmod(solc_usr_var8, solc_usr_var11, solc_usr_r)
                                let solc_usr_var13 := 0x333f8046ece5579cbd6872449c57f2703dfc8864cfadc06d587ff104a0d0c1f2
                                let solc_usr_a_3 := mload(0x8580)
                                let solc_usr_var14 := solc_usr_q_pow5(solc_usr_a_3)
                                let solc_usr_var15 := mulmod(solc_usr_var13, solc_usr_var14, solc_usr_r)
                                let solc_usr_var16 := addmod(solc_usr_var12, solc_usr_var15, solc_usr_r)
                                let solc_usr_var17 := 0x412c98232b6ab8a47aa76ee814ef7ec6261987c9802f2cfc490e007951a60ca5
                                let solc_usr_a_4 := mload(0x85a0)
                                let solc_usr_var18 := solc_usr_q_pow5(solc_usr_a_4)
                                let solc_usr_var19 := mulmod(solc_usr_var17, solc_usr_var18, solc_usr_r)
                                let solc_usr_var20 := addmod(solc_usr_var16, solc_usr_var19, solc_usr_r)
                                let solc_usr_var21 := 0x53fded36d490ba6b05a5d10fd99ffe5456baec6a6a8753199d5ebdc33c99790e
                                let solc_usr_a_5 := mload(0x8620)
                                let solc_usr_var22 := solc_usr_q_pow5(solc_usr_a_5)
                                let solc_usr_var23 := mulmod(solc_usr_var21, solc_usr_var22, solc_usr_r)
                                let solc_usr_var24 := addmod(solc_usr_var20, solc_usr_var23, solc_usr_r)
                                let solc_usr_var25 := 0x6ccb1c7d87f3c12a2bde4e68ac7f1e8b03481ba15d7f88f9a7f9b8310dd6d34
                                let solc_usr_a_6 := mload(0x8640)
                                let solc_usr_var26 := solc_usr_q_pow5(solc_usr_a_6)
                                let solc_usr_var27 := mulmod(solc_usr_var25, solc_usr_var26, solc_usr_r)
                                let solc_usr_var28 := addmod(solc_usr_var24, solc_usr_var27, solc_usr_r)
                                let solc_usr_var29 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                                let solc_usr_a_7 := mload(0x8660)
                                let solc_usr_var30 := solc_usr_q_pow5(solc_usr_a_7)
                                let solc_usr_var31 := mulmod(solc_usr_var29, solc_usr_var30, solc_usr_r)
                                let solc_usr_var32 := addmod(solc_usr_var28, solc_usr_var31, solc_usr_r)
                                let solc_usr_var33 := addmod(mulmod(0, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var32, solc_usr_r)
                                let solc_usr_f_1 := mload(0x8b00)
                                let solc_usr_a_1_next_1 := mload(0x85e0)
                                let solc_usr_var34 := mulmod(solc_usr_a_1_next_1, solc_usr_var0, solc_usr_r)
                                let solc_usr_var35 := addmod(solc_usr_f_1, solc_usr_var34, solc_usr_r)
                                let solc_usr_var36 := 0x5b1fc262a28cbb8bf75d9b1a6edaa74591ec24cd9a209512213cec3a3c0f1a5d
                                let solc_usr_var37 := mulmod(solc_usr_var36, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var38 := addmod(solc_usr_var35, solc_usr_var37, solc_usr_r)
                                let solc_usr_var39 := 0x4d0ea7f9c3fda06d9535b0fdafd8338bd47c2200b284fa71a325ff41ac358028
                                let solc_usr_var40 := mulmod(solc_usr_var39, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var41 := addmod(solc_usr_var38, solc_usr_var40, solc_usr_r)
                                let solc_usr_var42 := 0x26cc223e16f47c20e17cc6069605fa5a8af05ea4f6eb36029a641d23b818eb10
                                let solc_usr_var43 := mulmod(solc_usr_var42, solc_usr_var10, solc_usr_r)
                                let solc_usr_var44 := addmod(solc_usr_var41, solc_usr_var43, solc_usr_r)
                                let solc_usr_var45 := 0x31e823a45e567484c1544e310c0fa5cd66547a8f0dde659ac61698c30e838d25
                                let solc_usr_var46 := mulmod(solc_usr_var45, solc_usr_var14, solc_usr_r)
                                let solc_usr_var47 := addmod(solc_usr_var44, solc_usr_var46, solc_usr_r)
                                let solc_usr_var48 := 0x275a20361ea91992193920270d3e2d1f6361880ac0a439c64bef815d4469ba85
                                let solc_usr_var49 := mulmod(solc_usr_var48, solc_usr_var18, solc_usr_r)
                                let solc_usr_var50 := addmod(solc_usr_var47, solc_usr_var49, solc_usr_r)
                                let solc_usr_var51 := 0x5f3a15bab4ce4097b1edc3a25002694b92395ce355a8a12fe557459d9633f701
                                let solc_usr_var52 := mulmod(solc_usr_var51, solc_usr_var22, solc_usr_r)
                                let solc_usr_var53 := addmod(solc_usr_var50, solc_usr_var52, solc_usr_r)
                                let solc_usr_var54 := 0x301cf56f9b4577112cc4241cddf6484aaadedbf1bbd0f2351adf2e41c2fb2ecd
                                let solc_usr_var55 := mulmod(solc_usr_var54, solc_usr_var26, solc_usr_r)
                                let solc_usr_var56 := addmod(solc_usr_var53, solc_usr_var55, solc_usr_r)
                                let solc_usr_var57 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                                let solc_usr_var58 := mulmod(solc_usr_var57, solc_usr_var30, solc_usr_r)
                                let solc_usr_var59 := addmod(solc_usr_var56, solc_usr_var58, solc_usr_r)
                                let solc_usr_var60 := addmod(mulmod(solc_usr_var33, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var59, solc_usr_r)
                                let solc_usr_f_2 := mload(0x8b20)
                                let solc_usr_var61 := mulmod(solc_usr_a_3, solc_usr_var0, solc_usr_r)
                                let solc_usr_var62 := addmod(solc_usr_f_2, solc_usr_var61, solc_usr_r)
                                let solc_usr_var63 := 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140
                                let solc_usr_var64 := mulmod(solc_usr_var63, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var65 := addmod(solc_usr_var62, solc_usr_var64, solc_usr_r)
                                let solc_usr_var66 := 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a
                                let solc_usr_var67 := mulmod(solc_usr_var66, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var68 := addmod(solc_usr_var65, solc_usr_var67, solc_usr_r)
                                let solc_usr_var69 := 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db
                                let solc_usr_var70 := mulmod(solc_usr_var69, solc_usr_var10, solc_usr_r)
                                let solc_usr_var71 := addmod(solc_usr_var68, solc_usr_var70, solc_usr_r)
                                let solc_usr_var72 := addmod(mulmod(solc_usr_var60, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var71, solc_usr_r)
                                let solc_usr_f_3 := mload(0x8b40)
                                let solc_usr_var73 := mulmod(solc_usr_a_4, solc_usr_var0, solc_usr_r)
                                let solc_usr_var74 := addmod(solc_usr_f_3, solc_usr_var73, solc_usr_r)
                                let solc_usr_var75 := 0x222e83e70453dfee19b402e9fa8dfe2c4987b034d0be3ceb478b3022e97934c1
                                let solc_usr_var76 := mulmod(solc_usr_var75, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var77 := addmod(solc_usr_var74, solc_usr_var76, solc_usr_r)
                                let solc_usr_var78 := 0x26c2cc87f95726b28f33ca03409a460ec987cfe12adae32769e3565865d07191
                                let solc_usr_var79 := mulmod(solc_usr_var78, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var80 := addmod(solc_usr_var77, solc_usr_var79, solc_usr_r)
                                let solc_usr_var81 := 0x4382d0938a760120dd6cef8f3b90a0c38abae475e3d21e39365472b76d780272
                                let solc_usr_var82 := mulmod(solc_usr_var81, solc_usr_var10, solc_usr_r)
                                let solc_usr_var83 := addmod(solc_usr_var80, solc_usr_var82, solc_usr_r)
                                let solc_usr_var84 := mulmod(solc_usr_var69, solc_usr_var14, solc_usr_r)
                                let solc_usr_var85 := addmod(solc_usr_var83, solc_usr_var84, solc_usr_r)
                                let solc_usr_var86 := addmod(mulmod(solc_usr_var72, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var85, solc_usr_r)
                                let solc_usr_f_4 := mload(0x8a40)
                                let solc_usr_var87 := mulmod(solc_usr_a_5, solc_usr_var0, solc_usr_r)
                                let solc_usr_var88 := addmod(solc_usr_f_4, solc_usr_var87, solc_usr_r)
                                let solc_usr_var89 := 0x726df1506749848155630b86ae25a82b281ecd050fe3a52d85a181fa87202e4b
                                let solc_usr_var90 := mulmod(solc_usr_var89, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var91 := addmod(solc_usr_var88, solc_usr_var90, solc_usr_r)
                                let solc_usr_var92 := 0x24822e1af9aa2887c912c87eb0f20bd332330e7e55cd784de67cb407a9f05520
                                let solc_usr_var93 := mulmod(solc_usr_var92, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var94 := addmod(solc_usr_var91, solc_usr_var93, solc_usr_r)
                                let solc_usr_var95 := 0x4e5280109d8f96b8bfb543a6b1af25fb56a9db616af85a90eedc558e3eb1ea29
                                let solc_usr_var96 := mulmod(solc_usr_var95, solc_usr_var10, solc_usr_r)
                                let solc_usr_var97 := addmod(solc_usr_var94, solc_usr_var96, solc_usr_r)
                                let solc_usr_var98 := mulmod(solc_usr_var81, solc_usr_var14, solc_usr_r)
                                let solc_usr_var99 := addmod(solc_usr_var97, solc_usr_var98, solc_usr_r)
                                let solc_usr_var100 := mulmod(solc_usr_var69, solc_usr_var18, solc_usr_r)
                                let solc_usr_var101 := addmod(solc_usr_var99, solc_usr_var100, solc_usr_r)
                                let solc_usr_var102 := addmod(mulmod(solc_usr_var86, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var101, solc_usr_r)
                                let solc_usr_f_5 := mload(0x8a60)
                                let solc_usr_var103 := mulmod(solc_usr_a_6, solc_usr_var0, solc_usr_r)
                                let solc_usr_var104 := addmod(solc_usr_f_5, solc_usr_var103, solc_usr_r)
                                let solc_usr_var105 := 0x2f5908b169c6cf1bd26dcf0f9e5105481f5164f3ece0582bf3098312167751a7
                                let solc_usr_var106 := mulmod(solc_usr_var105, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var107 := addmod(solc_usr_var104, solc_usr_var106, solc_usr_r)
                                let solc_usr_var108 := 0x23a6684b942d726a22e4d5b8d8ff83aeaa773f62600184efe5d033d7c7c6e827
                                let solc_usr_var109 := mulmod(solc_usr_var108, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var110 := addmod(solc_usr_var107, solc_usr_var109, solc_usr_r)
                                let solc_usr_var111 := 0x1981b4b33d6a9dab957b351d981d3323e65da39493af5bc01f7e8ffe17f98d4e
                                let solc_usr_var112 := mulmod(solc_usr_var111, solc_usr_var10, solc_usr_r)
                                let solc_usr_var113 := addmod(solc_usr_var110, solc_usr_var112, solc_usr_r)
                                let solc_usr_var114 := mulmod(solc_usr_var95, solc_usr_var14, solc_usr_r)
                                let solc_usr_var115 := addmod(solc_usr_var113, solc_usr_var114, solc_usr_r)
                                let solc_usr_var116 := mulmod(solc_usr_var81, solc_usr_var18, solc_usr_r)
                                let solc_usr_var117 := addmod(solc_usr_var115, solc_usr_var116, solc_usr_r)
                                let solc_usr_var118 := mulmod(solc_usr_var69, solc_usr_var22, solc_usr_r)
                                let solc_usr_var119 := addmod(solc_usr_var117, solc_usr_var118, solc_usr_r)
                                let solc_usr_var120 := addmod(mulmod(solc_usr_var102, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var119, solc_usr_r)
                                let solc_usr_f_6 := mload(0x8a80)
                                let solc_usr_var121 := mulmod(solc_usr_a_7, solc_usr_var0, solc_usr_r)
                                let solc_usr_var122 := addmod(solc_usr_f_6, solc_usr_var121, solc_usr_r)
                                let solc_usr_var123 := 0x6d05a41959f539a7fc9ec0972ea1e3dbb6fc67dd51daf3414f7fbbb091c7274a
                                let solc_usr_var124 := mulmod(solc_usr_var123, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var125 := addmod(solc_usr_var122, solc_usr_var124, solc_usr_r)
                                let solc_usr_var126 := 0x27e7119226c42a6d19c1541904b99ae40685511ed2e078964b74594d38340849
                                let solc_usr_var127 := mulmod(solc_usr_var126, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var128 := addmod(solc_usr_var125, solc_usr_var127, solc_usr_r)
                                let solc_usr_var129 := 0xd94c46a8456352aa44d7a885ab59e3a36664e6fb25e826f8a4cd79822f0533
                                let solc_usr_var130 := mulmod(solc_usr_var129, solc_usr_var10, solc_usr_r)
                                let solc_usr_var131 := addmod(solc_usr_var128, solc_usr_var130, solc_usr_r)
                                let solc_usr_var132 := mulmod(solc_usr_var111, solc_usr_var14, solc_usr_r)
                                let solc_usr_var133 := addmod(solc_usr_var131, solc_usr_var132, solc_usr_r)
                                let solc_usr_var134 := mulmod(solc_usr_var95, solc_usr_var18, solc_usr_r)
                                let solc_usr_var135 := addmod(solc_usr_var133, solc_usr_var134, solc_usr_r)
                                let solc_usr_var136 := mulmod(solc_usr_var81, solc_usr_var22, solc_usr_r)
                                let solc_usr_var137 := addmod(solc_usr_var135, solc_usr_var136, solc_usr_r)
                                let solc_usr_var138 := mulmod(solc_usr_var69, solc_usr_var26, solc_usr_r)
                                let solc_usr_var139 := addmod(solc_usr_var137, solc_usr_var138, solc_usr_r)
                                let solc_usr_var140 := addmod(mulmod(solc_usr_var120, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var139, solc_usr_r)
                                let solc_usr_f_7 := mload(0x8aa0)
                                let solc_usr_a_2_next_1 := mload(0x8600)
                                let solc_usr_var141 := mulmod(solc_usr_a_2_next_1, solc_usr_var0, solc_usr_r)
                                let solc_usr_var142 := addmod(solc_usr_f_7, solc_usr_var141, solc_usr_r)
                                let solc_usr_var143 := 0x70d8f2a733a64d650faccc9b1c2a766a9544bb3ff1a11ee73cb43947ef386633
                                let solc_usr_var144 := mulmod(solc_usr_var143, solc_usr_a_0, solc_usr_r)
                                let solc_usr_var145 := addmod(solc_usr_var142, solc_usr_var144, solc_usr_r)
                                let solc_usr_var146 := 0x40fa389feb2522bb934881ac9ed749aee2296502af592418c6b5675c0f560261
                                let solc_usr_var147 := mulmod(solc_usr_var146, solc_usr_a_1, solc_usr_r)
                                let solc_usr_var148 := addmod(solc_usr_var145, solc_usr_var147, solc_usr_r)
                                let solc_usr_var149 := 0x1f61345b652161410c5e29f51e301ae56342af824bc110649393d2b911c50d3e
                                let solc_usr_var150 := mulmod(solc_usr_var149, solc_usr_var10, solc_usr_r)
                                let solc_usr_var151 := addmod(solc_usr_var148, solc_usr_var150, solc_usr_r)
                                let solc_usr_var152 := mulmod(solc_usr_var129, solc_usr_var14, solc_usr_r)
                                let solc_usr_var153 := addmod(solc_usr_var151, solc_usr_var152, solc_usr_r)
                                let solc_usr_var154 := mulmod(solc_usr_var111, solc_usr_var18, solc_usr_r)
                                let solc_usr_var155 := addmod(solc_usr_var153, solc_usr_var154, solc_usr_r)
                                let solc_usr_var156 := mulmod(solc_usr_var95, solc_usr_var22, solc_usr_r)
                                let solc_usr_var157 := addmod(solc_usr_var155, solc_usr_var156, solc_usr_r)
                                let solc_usr_var158 := mulmod(solc_usr_var81, solc_usr_var26, solc_usr_r)
                                let solc_usr_var159 := addmod(solc_usr_var157, solc_usr_var158, solc_usr_r)
                                let solc_usr_var160 := mulmod(solc_usr_var69, solc_usr_var30, solc_usr_r)
                                let solc_usr_var161 := addmod(solc_usr_var159, solc_usr_var160, solc_usr_r)
                                let solc_usr_var162 := addmod(mulmod(solc_usr_var140, solc_usr_q_trash_tau, solc_usr_r), solc_usr_var161, solc_usr_r)
                                let solc_usr_f_26 := mload(0x8c20)
                                let solc_usr_q_trash_one_minus_selector := addmod(1, sub(solc_usr_r, solc_usr_f_26), solc_usr_r)
                                let solc_usr_q_trash_scaled := mulmod(solc_usr_q_trash_one_minus_selector, mload(0x91a0), solc_usr_r)
                                let solc_usr_q_trash_eval := addmod(solc_usr_var162, sub(solc_usr_r, solc_usr_q_trash_scaled), solc_usr_r)
                                mstore(0xa300, mulmod(mload(0xa300), solc_usr_y, solc_usr_r))
                                mstore(0xa300, addmod(mload(0xa300), solc_usr_q_trash_eval, solc_usr_r))
                            }
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x00)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0600)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x20)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x05e0)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x40)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0580)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x60)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0520)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x80)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x04c0)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0xa0)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0460)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0xc0)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0400)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0xe0)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x03a0)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x0100)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0340)), solc_usr_r))
                        }
                        {
                            let solc_usr_q_sel_ptr := add(41408, 0x0120)
                            mstore(solc_usr_q_sel_ptr, mulmod(mload(solc_usr_q_sel_ptr), mload(add(0xa340, 0x0280)), solc_usr_r))
                        }
                        let solc_usr_linearization_expected_eval := addmod(0, sub(solc_usr_r, mload(0xa300)), solc_usr_r)
                        mstore(28032, solc_usr_linearization_expected_eval)
                        pop(solc_usr_y)
                    }
                    {
                        let solc_usr_x := mload(27168)
                        let solc_usr_k := 20
                        let solc_usr_x_pow_2i := solc_usr_x
                        let solc_usr_x_pow_2i_minus1 := 1
                        for { let solc_usr_idx := 0 }
                        lt(solc_usr_idx, solc_usr_k)
                        { solc_usr_idx := add(solc_usr_idx, 1) }
                        {
                            solc_usr_x_pow_2i_minus1 := mulmod(mulmod(solc_usr_x_pow_2i_minus1, solc_usr_x_pow_2i_minus1, solc_usr_r), solc_usr_x, solc_usr_r)
                            solc_usr_x_pow_2i := mulmod(solc_usr_x_pow_2i, solc_usr_x_pow_2i, solc_usr_r)
                        }
                        let solc_usr_x_split := solc_usr_x_pow_2i_minus1
                        let solc_usr_one_minus_x_n := addmod(1, sub(solc_usr_r, solc_usr_x_pow_2i), solc_usr_r)
                        mstore(28064, solc_usr_x_split)
                        mstore(add(28064, 0x20), solc_usr_one_minus_x_n)
                    }
                    {
                        {
                            let solc_usr_x := mload(27168)
                            let solc_usr_omega := mload(10112)
                            let solc_usr_omega_inv := mload(10144)
                            let solc_usr_x_pow_of_omega := solc_usr_x
                            mstore(add(28672, 0x40), solc_usr_x_pow_of_omega)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega, solc_usr_r)
                            mstore(add(28672, 0x60), solc_usr_x_pow_of_omega)
                            solc_usr_x_pow_of_omega := solc_usr_x
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            mstore(add(28672, 0x20), solc_usr_x_pow_of_omega)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            solc_usr_x_pow_of_omega := mulmod(solc_usr_x_pow_of_omega, solc_usr_omega_inv, solc_usr_r)
                            mstore(add(28672, 0x0), solc_usr_x_pow_of_omega)
                        }
                        {
                            let solc_usr_x1 := mload(27200)
                            mstore(29568, 1)
                            let solc_usr_acc := 1
                            let solc_usr_p := 29568
                            for { let solc_usr_i := 0 } lt(solc_usr_i, 0x2a) { solc_usr_i := add(solc_usr_i, 1) }
                            {
                                solc_usr_p := add(solc_usr_p, 0x20)
                                solc_usr_acc := mulmod(solc_usr_acc, solc_usr_x1, solc_usr_r)
                                mstore(solc_usr_p, and(solc_usr_acc, 0xffffffffffffffffffffffffffffffff))
                            }
                        }
                        {
                            mstore(0xa300, 0x8a00)
                            mstore(0xa320, 0x8500)
                            mstore(0xa340, 0x90a0)
                            mstore(0xa360, 0x90c0)
                            mstore(0xa380, 0x9120)
                            mstore(0xa3a0, 0x9140)
                            mstore(0xa3c0, 0x91a0)
                            mstore(0xa3e0, 0x8a20)
                            mstore(0xa400, 0x8a40)
                            mstore(0xa420, 0x8a60)
                            mstore(0xa440, 0x8a80)
                            mstore(0xa460, 0x8aa0)
                            mstore(0xa480, 0x8ac0)
                            mstore(0xa4a0, 0x8ae0)
                            mstore(0xa4c0, 0x8b00)
                            mstore(0xa4e0, 0x8b20)
                            mstore(0xa500, 0x8b40)
                            mstore(0xa520, 0x8b60)
                            mstore(0xa540, 0x8b80)
                            mstore(0xa560, 0x8ba0)
                            mstore(0xa580, 0x8bc0)
                            mstore(0xa5a0, 0x8be0)
                            mstore(0xa5c0, 0x8c00)
                            mstore(0xa5e0, 0x8c20)
                            mstore(0xa600, 0x8c40)
                            mstore(0xa620, 0x8c60)
                            mstore(0xa640, 0x8c80)
                            mstore(0xa660, 0x8ca0)
                            mstore(0xa680, 0x8cc0)
                            mstore(0xa6a0, 0x8ce0)
                            mstore(0xa6c0, 0x8d00)
                            mstore(0xa6e0, 0x8d20)
                            mstore(0xa700, 0x8d40)
                            mstore(0xa720, 0x8d60)
                            mstore(0xa740, 0x8d80)
                            mstore(0xa760, 0x8da0)
                            mstore(0xa780, 0x8dc0)
                            mstore(0xa7a0, 0x8de0)
                            mstore(0xa7c0, 0x8e00)
                            mstore(0xa7e0, 0x8e20)
                            mstore(0xa800, 0x8e40)
                            mstore(0xa820, 0x8e60)
                            mstore(0xa840, 28032)
                            let solc_usr_q_eval_set_0 := mload(0x8a00)
                            let solc_usr_pow_p := add(29568, 0x20)
                            let solc_usr_eval_p := add(0xa300, 0x20)
                            for { let solc_usr_i := 1 } lt(solc_usr_i, 0x2b) { solc_usr_i := add(solc_usr_i, 1) }
                            {
                                let solc_usr_pow := mload(solc_usr_pow_p)
                                solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(mload(solc_usr_eval_p)), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_pow_p := add(solc_usr_pow_p, 0x20)
                                solc_usr_eval_p := add(solc_usr_eval_p, 0x20)
                            }
                            mstore(add(31648, 0x0), solc_usr_q_eval_set_0)
                        }
                        {
                            let solc_usr_q_eval_set_0 := mload(0x86e0)
                            let solc_usr_q_eval_set_1 := mload(0x89a0)
                            solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(0x8700), mload(add(29568, 0x20)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(0x89c0), mload(add(29568, 0x20)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(0x8720), mload(add(29568, 0x40)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(0x89e0), mload(add(29568, 0x40)), solc_usr_r), solc_usr_r)
                            mstore(add(31648, 0x20), solc_usr_q_eval_set_0)
                            mstore(add(31648, 0x40), solc_usr_q_eval_set_1)
                        }
                        {
                            let solc_usr_q_eval_set_0 := mload(0x9060)
                            let solc_usr_q_eval_set_1 := mload(0x9080)
                            solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(0x90e0), mload(add(29568, 0x20)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(0x9100), mload(add(29568, 0x20)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(0x9160), mload(add(29568, 0x40)), solc_usr_r), solc_usr_r)
                            solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(0x9180), mload(add(29568, 0x40)), solc_usr_r), solc_usr_r)
                            mstore(add(31648, 0x60), solc_usr_q_eval_set_0)
                            mstore(add(31648, 0x80), solc_usr_q_eval_set_1)
                        }
                        {
                            mstore(0xa300, 0x8520)
                            mstore(0xa320, 0x85c0)
                            mstore(0xa340, 0x8840)
                            mstore(0xa360, 0x8540)
                            mstore(0xa380, 0x85e0)
                            mstore(0xa3a0, 0x8860)
                            mstore(0xa3c0, 0x8560)
                            mstore(0xa3e0, 0x8600)
                            mstore(0xa400, 0x8880)
                            mstore(0xa420, 0x8580)
                            mstore(0xa440, 0x8740)
                            mstore(0xa460, 0x88a0)
                            mstore(0xa480, 0x85a0)
                            mstore(0xa4a0, 0x8760)
                            mstore(0xa4c0, 0x88c0)
                            mstore(0xa4e0, 0x8620)
                            mstore(0xa500, 0x8780)
                            mstore(0xa520, 0x88e0)
                            mstore(0xa540, 0x8640)
                            mstore(0xa560, 0x87a0)
                            mstore(0xa580, 0x8900)
                            mstore(0xa5a0, 0x8660)
                            mstore(0xa5c0, 0x87c0)
                            mstore(0xa5e0, 0x8920)
                            mstore(0xa600, 0x8680)
                            mstore(0xa620, 0x87e0)
                            mstore(0xa640, 0x8940)
                            mstore(0xa660, 0x86a0)
                            mstore(0xa680, 0x8800)
                            mstore(0xa6a0, 0x8960)
                            mstore(0xa6c0, 0x86c0)
                            mstore(0xa6e0, 0x8820)
                            mstore(0xa700, 0x8980)
                            let solc_usr_q_eval_set_0 := mload(0x8520)
                            let solc_usr_q_eval_set_1 := mload(0x85c0)
                            let solc_usr_q_eval_set_2 := mload(0x8840)
                            let solc_usr_pow_p := add(29568, 0x20)
                            let solc_usr_eval_p := add(0xa300, 0x60)
                            for { let solc_usr_i := 1 } lt(solc_usr_i, 0xb) { solc_usr_i := add(solc_usr_i, 1) }
                            {
                                let solc_usr_pow := mload(solc_usr_pow_p)
                                solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(mload(solc_usr_eval_p)), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(mload(add(solc_usr_eval_p, 0x20))), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_q_eval_set_2 := addmod(solc_usr_q_eval_set_2, mulmod(mload(mload(add(solc_usr_eval_p, 0x40))), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_pow_p := add(solc_usr_pow_p, 0x20)
                                solc_usr_eval_p := add(solc_usr_eval_p, 0x60)
                            }
                            mstore(add(31648, 0xa0), solc_usr_q_eval_set_0)
                            mstore(add(31648, 0xc0), solc_usr_q_eval_set_1)
                            mstore(add(31648, 0xe0), solc_usr_q_eval_set_2)
                        }
                        {
                            mstore(0xa300, 0x8e80)
                            mstore(0xa320, 0x8ea0)
                            mstore(0xa340, 0x8ec0)
                            mstore(0xa360, 0x8ee0)
                            mstore(0xa380, 0x8f00)
                            mstore(0xa3a0, 0x8f20)
                            mstore(0xa3c0, 0x8f40)
                            mstore(0xa3e0, 0x8f60)
                            mstore(0xa400, 0x8f80)
                            mstore(0xa420, 0x8fa0)
                            mstore(0xa440, 0x8fc0)
                            mstore(0xa460, 0x8fe0)
                            mstore(0xa480, 0x9000)
                            mstore(0xa4a0, 0x9020)
                            mstore(0xa4c0, 0x9040)
                            let solc_usr_q_eval_set_0 := mload(0x8e80)
                            let solc_usr_q_eval_set_1 := mload(0x8ea0)
                            let solc_usr_q_eval_set_2 := mload(0x8ec0)
                            let solc_usr_pow_p := add(29568, 0x20)
                            let solc_usr_eval_p := add(0xa300, 0x60)
                            for { let solc_usr_i := 1 } lt(solc_usr_i, 0x5) { solc_usr_i := add(solc_usr_i, 1) }
                            {
                                let solc_usr_pow := mload(solc_usr_pow_p)
                                solc_usr_q_eval_set_0 := addmod(solc_usr_q_eval_set_0, mulmod(mload(mload(solc_usr_eval_p)), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_q_eval_set_1 := addmod(solc_usr_q_eval_set_1, mulmod(mload(mload(add(solc_usr_eval_p, 0x20))), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_q_eval_set_2 := addmod(solc_usr_q_eval_set_2, mulmod(mload(mload(add(solc_usr_eval_p, 0x40))), solc_usr_pow, solc_usr_r), solc_usr_r)
                                solc_usr_pow_p := add(solc_usr_pow_p, 0x20)
                                solc_usr_eval_p := add(solc_usr_eval_p, 0x60)
                            }
                            mstore(add(31648, 0x100), solc_usr_q_eval_set_0)
                            mstore(add(31648, 0x120), solc_usr_q_eval_set_1)
                            mstore(add(31648, 0x140), solc_usr_q_eval_set_2)
                        }
                        {
                            let solc_usr_x2 := mload(27232)
                            let solc_usr_x3 := mload(27264)
                            let solc_usr_f_eval := 0
                            let solc_usr_Q_EVAL_CPTR := mload(33440)
                            let solc_usr_rot_pt_0 := mload(add(28672, 0x0))
                            let solc_usr_rot_pt_1 := mload(add(28672, 0x20))
                            let solc_usr_rot_pt_2 := mload(add(28672, 0x40))
                            let solc_usr_rot_pt_3 := mload(add(28672, 0x60))
                            {
                                let solc_usr_dx_0 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r)
                                let solc_usr_dx_1 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r)
                                let solc_usr_dx_2 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_0), solc_usr_r)
                                let solc_usr_lbasis_0 := 1
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_0), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_1 := 1
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_3, sub(solc_usr_r, solc_usr_rot_pt_0), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_2 := 1
                                solc_usr_lbasis_2 := mulmod(solc_usr_lbasis_2, addmod(solc_usr_rot_pt_0, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_2 := mulmod(solc_usr_lbasis_2, addmod(solc_usr_rot_pt_0, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r), solc_usr_r)
                                let solc_usr_bp_0 := solc_usr_dx_0
                                let solc_usr_bp_1 := mulmod(solc_usr_bp_0, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_bp_2 := mulmod(solc_usr_bp_1, solc_usr_dx_2, solc_usr_r)
                                let solc_usr_bp_3 := mulmod(solc_usr_bp_2, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_bp_4 := mulmod(solc_usr_bp_3, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_bp_5 := mulmod(solc_usr_bp_4, solc_usr_lbasis_2, solc_usr_r)
                                let solc_usr_bq := solc_usr_scalar_inv(solc_usr_bp_5)
                                let solc_usr_lbasis_inv_2 := mulmod(solc_usr_bq, solc_usr_bp_4, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_2, solc_usr_r)
                                let solc_usr_lbasis_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_3, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_lbasis_inv_0 := mulmod(solc_usr_bq, solc_usr_bp_2, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_dx_inv_2 := mulmod(solc_usr_bq, solc_usr_bp_1, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_2, solc_usr_r)
                                let solc_usr_dx_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_0, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_dx_inv_0 := solc_usr_bq
                                let solc_usr_den_inv := solc_usr_dx_inv_0
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_1, solc_usr_r)
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_2, solc_usr_r)
                                let solc_usr_eval := mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x80)), solc_usr_den_inv, solc_usr_r)
                                let solc_usr_term_0 := mulmod(mulmod(mload(add(31648, 0x100)), solc_usr_dx_inv_0, solc_usr_r), solc_usr_lbasis_inv_0, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_0), solc_usr_r)
                                let solc_usr_term_1 := mulmod(mulmod(mload(add(31648, 0x120)), solc_usr_dx_inv_1, solc_usr_r), solc_usr_lbasis_inv_1, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_1), solc_usr_r)
                                let solc_usr_term_2 := mulmod(mulmod(mload(add(31648, 0x140)), solc_usr_dx_inv_2, solc_usr_r), solc_usr_lbasis_inv_2, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_2), solc_usr_r)
                                solc_usr_f_eval := addmod(mulmod(solc_usr_f_eval, solc_usr_x2, solc_usr_r), solc_usr_eval, solc_usr_r)
                            }
                            {
                                let solc_usr_dx_0 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r)
                                let solc_usr_dx_1 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r)
                                let solc_usr_dx_2 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_1), solc_usr_r)
                                let solc_usr_lbasis_0 := 1
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_1), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_1 := 1
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_3, sub(solc_usr_r, solc_usr_rot_pt_1), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_2 := 1
                                solc_usr_lbasis_2 := mulmod(solc_usr_lbasis_2, addmod(solc_usr_rot_pt_1, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                solc_usr_lbasis_2 := mulmod(solc_usr_lbasis_2, addmod(solc_usr_rot_pt_1, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r), solc_usr_r)
                                let solc_usr_bp_0 := solc_usr_dx_0
                                let solc_usr_bp_1 := mulmod(solc_usr_bp_0, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_bp_2 := mulmod(solc_usr_bp_1, solc_usr_dx_2, solc_usr_r)
                                let solc_usr_bp_3 := mulmod(solc_usr_bp_2, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_bp_4 := mulmod(solc_usr_bp_3, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_bp_5 := mulmod(solc_usr_bp_4, solc_usr_lbasis_2, solc_usr_r)
                                let solc_usr_bq := solc_usr_scalar_inv(solc_usr_bp_5)
                                let solc_usr_lbasis_inv_2 := mulmod(solc_usr_bq, solc_usr_bp_4, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_2, solc_usr_r)
                                let solc_usr_lbasis_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_3, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_lbasis_inv_0 := mulmod(solc_usr_bq, solc_usr_bp_2, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_dx_inv_2 := mulmod(solc_usr_bq, solc_usr_bp_1, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_2, solc_usr_r)
                                let solc_usr_dx_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_0, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_dx_inv_0 := solc_usr_bq
                                let solc_usr_den_inv := solc_usr_dx_inv_0
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_1, solc_usr_r)
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_2, solc_usr_r)
                                let solc_usr_eval := mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x60)), solc_usr_den_inv, solc_usr_r)
                                let solc_usr_term_0 := mulmod(mulmod(mload(add(31648, 0xa0)), solc_usr_dx_inv_0, solc_usr_r), solc_usr_lbasis_inv_0, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_0), solc_usr_r)
                                let solc_usr_term_1 := mulmod(mulmod(mload(add(31648, 0xc0)), solc_usr_dx_inv_1, solc_usr_r), solc_usr_lbasis_inv_1, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_1), solc_usr_r)
                                let solc_usr_term_2 := mulmod(mulmod(mload(add(31648, 0xe0)), solc_usr_dx_inv_2, solc_usr_r), solc_usr_lbasis_inv_2, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_2), solc_usr_r)
                                solc_usr_f_eval := addmod(mulmod(solc_usr_f_eval, solc_usr_x2, solc_usr_r), solc_usr_eval, solc_usr_r)
                            }
                            {
                                let solc_usr_dx_0 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r)
                                let solc_usr_dx_1 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r)
                                let solc_usr_lbasis_0 := 1
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_3), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_1 := 1
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                let solc_usr_bp_0 := solc_usr_dx_0
                                let solc_usr_bp_1 := mulmod(solc_usr_bp_0, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_bp_2 := mulmod(solc_usr_bp_1, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_bp_3 := mulmod(solc_usr_bp_2, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_bq := solc_usr_scalar_inv(solc_usr_bp_3)
                                let solc_usr_lbasis_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_2, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_lbasis_inv_0 := mulmod(solc_usr_bq, solc_usr_bp_1, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_dx_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_0, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_dx_inv_0 := solc_usr_bq
                                let solc_usr_den_inv := solc_usr_dx_inv_0
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_1, solc_usr_r)
                                let solc_usr_eval := mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x40)), solc_usr_den_inv, solc_usr_r)
                                let solc_usr_term_0 := mulmod(mulmod(mload(add(31648, 0x60)), solc_usr_dx_inv_0, solc_usr_r), solc_usr_lbasis_inv_0, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_0), solc_usr_r)
                                let solc_usr_term_1 := mulmod(mulmod(mload(add(31648, 0x80)), solc_usr_dx_inv_1, solc_usr_r), solc_usr_lbasis_inv_1, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_1), solc_usr_r)
                                solc_usr_f_eval := addmod(mulmod(solc_usr_f_eval, solc_usr_x2, solc_usr_r), solc_usr_eval, solc_usr_r)
                            }
                            {
                                let solc_usr_dx_0 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r)
                                let solc_usr_dx_1 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_1), solc_usr_r)
                                let solc_usr_lbasis_0 := 1
                                solc_usr_lbasis_0 := mulmod(solc_usr_lbasis_0, addmod(solc_usr_rot_pt_2, sub(solc_usr_r, solc_usr_rot_pt_1), solc_usr_r), solc_usr_r)
                                let solc_usr_lbasis_1 := 1
                                solc_usr_lbasis_1 := mulmod(solc_usr_lbasis_1, addmod(solc_usr_rot_pt_1, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r), solc_usr_r)
                                let solc_usr_bp_0 := solc_usr_dx_0
                                let solc_usr_bp_1 := mulmod(solc_usr_bp_0, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_bp_2 := mulmod(solc_usr_bp_1, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_bp_3 := mulmod(solc_usr_bp_2, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_bq := solc_usr_scalar_inv(solc_usr_bp_3)
                                let solc_usr_lbasis_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_2, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_1, solc_usr_r)
                                let solc_usr_lbasis_inv_0 := mulmod(solc_usr_bq, solc_usr_bp_1, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_lbasis_0, solc_usr_r)
                                let solc_usr_dx_inv_1 := mulmod(solc_usr_bq, solc_usr_bp_0, solc_usr_r)
                                solc_usr_bq := mulmod(solc_usr_bq, solc_usr_dx_1, solc_usr_r)
                                let solc_usr_dx_inv_0 := solc_usr_bq
                                let solc_usr_den_inv := solc_usr_dx_inv_0
                                solc_usr_den_inv := mulmod(solc_usr_den_inv, solc_usr_dx_inv_1, solc_usr_r)
                                let solc_usr_eval := mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x20)), solc_usr_den_inv, solc_usr_r)
                                let solc_usr_term_0 := mulmod(mulmod(mload(add(31648, 0x20)), solc_usr_dx_inv_0, solc_usr_r), solc_usr_lbasis_inv_0, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_0), solc_usr_r)
                                let solc_usr_term_1 := mulmod(mulmod(mload(add(31648, 0x40)), solc_usr_dx_inv_1, solc_usr_r), solc_usr_lbasis_inv_1, solc_usr_r)
                                solc_usr_eval := addmod(solc_usr_eval, sub(solc_usr_r, solc_usr_term_1), solc_usr_r)
                                solc_usr_f_eval := addmod(mulmod(solc_usr_f_eval, solc_usr_x2, solc_usr_r), solc_usr_eval, solc_usr_r)
                            }
                            {
                                let solc_usr_dx0 := addmod(solc_usr_x3, sub(solc_usr_r, solc_usr_rot_pt_2), solc_usr_r)
                                let solc_usr_dx0_inv := solc_usr_scalar_inv(solc_usr_dx0)
                                let solc_usr_eval := mulmod(addmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x0)), sub(solc_usr_r, mload(add(31648, 0x0))), solc_usr_r), solc_usr_dx0_inv, solc_usr_r)
                                solc_usr_f_eval := addmod(mulmod(solc_usr_f_eval, solc_usr_x2, solc_usr_r), solc_usr_eval, solc_usr_r)
                            }
                            mstore(28224, solc_usr_f_eval)
                        }
                        {
                            let solc_usr_x4 := mload(27296)
                            let solc_usr_lin_x_split := mload(28064)
                            let solc_usr_lin_one_minus_x_n := mload(add(28064, 0x20))
                            let solc_usr_Q_EVAL_CPTR := mload(33440)
                            let solc_usr_x4_pow_full := 1
                            solc_usr_x4_pow_full := mulmod(solc_usr_x4_pow_full, solc_usr_x4, solc_usr_r)
                            let solc_usr_x4_pow_1 := and(solc_usr_x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            solc_usr_x4_pow_full := mulmod(solc_usr_x4_pow_full, solc_usr_x4, solc_usr_r)
                            let solc_usr_x4_pow_2 := and(solc_usr_x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            solc_usr_x4_pow_full := mulmod(solc_usr_x4_pow_full, solc_usr_x4, solc_usr_r)
                            let solc_usr_x4_pow_3 := and(solc_usr_x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            solc_usr_x4_pow_full := mulmod(solc_usr_x4_pow_full, solc_usr_x4, solc_usr_r)
                            let solc_usr_x4_pow_4 := and(solc_usr_x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            solc_usr_x4_pow_full := mulmod(solc_usr_x4_pow_full, solc_usr_x4, solc_usr_r)
                            let solc_usr_x4_pow_5 := and(solc_usr_x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            let solc_usr_v := calldataload(solc_usr_Q_EVAL_CPTR)
                            solc_usr_v := addmod(solc_usr_v, mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x20)), solc_usr_x4_pow_1, solc_usr_r), solc_usr_r)
                            solc_usr_v := addmod(solc_usr_v, mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x40)), solc_usr_x4_pow_2, solc_usr_r), solc_usr_r)
                            solc_usr_v := addmod(solc_usr_v, mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x60)), solc_usr_x4_pow_3, solc_usr_r), solc_usr_r)
                            solc_usr_v := addmod(solc_usr_v, mulmod(calldataload(add(solc_usr_Q_EVAL_CPTR, 0x80)), solc_usr_x4_pow_4, solc_usr_r), solc_usr_r)
                            solc_usr_v := addmod(solc_usr_v, mulmod(mload(28224), solc_usr_x4_pow_5, solc_usr_r), solc_usr_r)
                            mcopy(0xa300, 0x98c0, 0x80)
                            mstore(0xa380, 1)
                            mcopy(0xa3a0, 0x9940, 0x80)
                            mstore(0xa420, mload(add(29568, 0x40)))
                            mcopy(0xa440, 0x9d40, 0x80)
                            mstore(0xa4c0, mload(add(29568, 0x60)))
                            mcopy(0xa4e0, 0x99c0, 0x80)
                            mstore(0xa560, mload(add(29568, 0x80)))
                            mcopy(0xa580, 0x9dc0, 0x80)
                            mstore(0xa600, mload(add(29568, 0xa0)))
                            mcopy(0xa620, 0x9f40, 0x80)
                            mstore(0xa6a0, mload(add(29568, 0xc0)))
                            mcopy(0xa6c0, 0x5780, 0x80)
                            mstore(0xa740, mload(add(29568, 0xe0)))
                            mcopy(0xa760, 0x5500, 0x80)
                            mstore(0xa7e0, mload(add(29568, 0x100)))
                            mcopy(0xa800, 0x5580, 0x80)
                            mstore(0xa880, mload(add(29568, 0x120)))
                            mcopy(0xa8a0, 0x5600, 0x80)
                            mstore(0xa920, mload(add(29568, 0x140)))
                            mcopy(0xa940, 0x5680, 0x80)
                            mstore(0xa9c0, mload(add(29568, 0x160)))
                            mcopy(0xa9e0, 0x5700, 0x80)
                            mstore(0xaa60, mload(add(29568, 0x180)))
                            mcopy(0xaa80, 0x5300, 0x80)
                            mstore(0xab00, mload(add(29568, 0x1a0)))
                            mcopy(0xab20, 0x5380, 0x80)
                            mstore(0xaba0, mload(add(29568, 0x1c0)))
                            mcopy(0xabc0, 0x5400, 0x80)
                            mstore(0xac40, mload(add(29568, 0x1e0)))
                            mcopy(0xac60, 0x5480, 0x80)
                            mstore(0xace0, mload(add(29568, 0x200)))
                            mcopy(0xad00, 0x5800, 0x80)
                            mstore(0xad80, mload(add(29568, 0x220)))
                            mcopy(0xada0, 0x5880, 0x80)
                            mstore(0xae20, mload(add(29568, 0x240)))
                            mcopy(0xae40, 0x5900, 0x80)
                            mstore(0xaec0, mload(add(29568, 0x260)))
                            mcopy(0xaee0, 0x5980, 0x80)
                            mstore(0xaf60, mload(add(29568, 0x280)))
                            mcopy(0xaf80, 0x5b80, 0x80)
                            mstore(0xb000, mload(add(29568, 0x2a0)))
                            mcopy(0xb020, 0x5f00, 0x80)
                            mstore(0xb0a0, mload(add(29568, 0x2c0)))
                            mcopy(0xb0c0, 0x6000, 0x80)
                            mstore(0xb140, mload(add(29568, 0x2e0)))
                            mcopy(0xb160, 0x6080, 0x80)
                            mstore(0xb1e0, mload(add(29568, 0x300)))
                            mcopy(0xb200, 0x6100, 0x80)
                            mstore(0xb280, mload(add(29568, 0x320)))
                            mcopy(0xb2a0, 0x6180, 0x80)
                            mstore(0xb320, mload(add(29568, 0x340)))
                            mcopy(0xb340, 0x6200, 0x80)
                            mstore(0xb3c0, mload(add(29568, 0x360)))
                            mcopy(0xb3e0, 0x6280, 0x80)
                            mstore(0xb460, mload(add(29568, 0x380)))
                            mcopy(0xb480, 0x6300, 0x80)
                            mstore(0xb500, mload(add(29568, 0x3a0)))
                            mcopy(0xb520, 0x6380, 0x80)
                            mstore(0xb5a0, mload(add(29568, 0x3c0)))
                            mcopy(0xb5c0, 0x6400, 0x80)
                            mstore(0xb640, mload(add(29568, 0x3e0)))
                            mcopy(0xb660, 0x6480, 0x80)
                            mstore(0xb6e0, mload(add(29568, 0x400)))
                            mcopy(0xb700, 0x6500, 0x80)
                            mstore(0xb780, mload(add(29568, 0x420)))
                            mcopy(0xb7a0, 0x6580, 0x80)
                            mstore(0xb820, mload(add(29568, 0x440)))
                            mcopy(0xb840, 0x6600, 0x80)
                            mstore(0xb8c0, mload(add(29568, 0x460)))
                            mcopy(0xb8e0, 0x6680, 0x80)
                            mstore(0xb960, mload(add(29568, 0x480)))
                            mcopy(0xb980, 0x6700, 0x80)
                            mstore(0xba00, mload(add(29568, 0x4a0)))
                            mcopy(0xba20, 0x6780, 0x80)
                            mstore(0xbaa0, mload(add(29568, 0x4c0)))
                            mcopy(0xbac0, 0x6800, 0x80)
                            mstore(0xbb40, mload(add(29568, 0x4e0)))
                            mcopy(0xbb60, 0x6880, 0x80)
                            mstore(0xbbe0, mload(add(29568, 0x500)))
                            mcopy(0xbc00, 0x6900, 0x80)
                            mstore(0xbc80, mload(add(29568, 0x520)))
                            let solc_usr_lin_query_scalar_41 := mload(add(29568, 0x540))
                            let solc_usr_lin_cur_scalar_41 := mulmod(solc_usr_lin_query_scalar_41, solc_usr_lin_one_minus_x_n, solc_usr_r)
                            mcopy(0xbca0, add(40896, 0x0), 0x80)
                            mstore(0xbd20, solc_usr_lin_cur_scalar_41)
                            solc_usr_lin_cur_scalar_41 := mulmod(solc_usr_lin_cur_scalar_41, solc_usr_lin_x_split, solc_usr_r)
                            mcopy(0xbd40, add(40896, 0x80), 0x80)
                            mstore(0xbdc0, solc_usr_lin_cur_scalar_41)
                            solc_usr_lin_cur_scalar_41 := mulmod(solc_usr_lin_cur_scalar_41, solc_usr_lin_x_split, solc_usr_r)
                            mcopy(0xbde0, add(40896, 0x100), 0x80)
                            mstore(0xbe60, solc_usr_lin_cur_scalar_41)
                            solc_usr_lin_cur_scalar_41 := mulmod(solc_usr_lin_cur_scalar_41, solc_usr_lin_x_split, solc_usr_r)
                            mcopy(0xbe80, add(40896, 0x180), 0x80)
                            mstore(0xbf00, solc_usr_lin_cur_scalar_41)
                            mcopy(0xbf20, 0x5a00, 0x80)
                            mstore(0xbfa0, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x0)), solc_usr_r))
                            mcopy(0xbfc0, 0x5a80, 0x80)
                            mstore(0xc040, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x20)), solc_usr_r))
                            mcopy(0xc060, 0x5b00, 0x80)
                            mstore(0xc0e0, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x40)), solc_usr_r))
                            mcopy(0xc100, 0x5c00, 0x80)
                            mstore(0xc180, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x60)), solc_usr_r))
                            mcopy(0xc1a0, 0x5c80, 0x80)
                            mstore(0xc220, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x80)), solc_usr_r))
                            mcopy(0xc240, 0x5d00, 0x80)
                            mstore(0xc2c0, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0xa0)), solc_usr_r))
                            mcopy(0xc2e0, 0x5d80, 0x80)
                            mstore(0xc360, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0xc0)), solc_usr_r))
                            mcopy(0xc380, 0x5e00, 0x80)
                            mstore(0xc400, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0xe0)), solc_usr_r))
                            mcopy(0xc420, 0x5e80, 0x80)
                            mstore(0xc4a0, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x100)), solc_usr_r))
                            mcopy(0xc4c0, 0x5f80, 0x80)
                            mstore(0xc540, mulmod(solc_usr_lin_query_scalar_41, mload(add(41408, 0x120)), solc_usr_r))
                            mcopy(0xc560, 0x9740, 0x80)
                            mstore(0xc5e0, solc_usr_x4_pow_1)
                            mcopy(0xc600, 0x97c0, 0x80)
                            mstore(0xc680, mulmod(mload(add(29568, 0x20)), solc_usr_x4_pow_1, solc_usr_r))
                            mcopy(0xc6a0, 0x9840, 0x80)
                            mstore(0xc720, mulmod(mload(add(29568, 0x40)), solc_usr_x4_pow_1, solc_usr_r))
                            mcopy(0xc740, 0x9cc0, 0x80)
                            mstore(0xc7c0, solc_usr_x4_pow_2)
                            mcopy(0xc7e0, 0x9e40, 0x80)
                            mstore(0xc860, mulmod(mload(add(29568, 0x20)), solc_usr_x4_pow_2, solc_usr_r))
                            mcopy(0xc880, 0x9ec0, 0x80)
                            mstore(0xc900, mulmod(mload(add(29568, 0x40)), solc_usr_x4_pow_2, solc_usr_r))
                            mcopy(0xc920, 0x91c0, 0x80)
                            mstore(0xc9a0, solc_usr_x4_pow_3)
                            mcopy(0xc9c0, 0x9240, 0x80)
                            mstore(0xca40, mulmod(mload(add(29568, 0x20)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xca60, 0x92c0, 0x80)
                            mstore(0xcae0, mulmod(mload(add(29568, 0x40)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcb00, 0x9340, 0x80)
                            mstore(0xcb80, mulmod(mload(add(29568, 0x60)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcba0, 0x93c0, 0x80)
                            mstore(0xcc20, mulmod(mload(add(29568, 0x80)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcc40, 0x9440, 0x80)
                            mstore(0xccc0, mulmod(mload(add(29568, 0xa0)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcce0, 0x94c0, 0x80)
                            mstore(0xcd60, mulmod(mload(add(29568, 0xc0)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcd80, 0x9540, 0x80)
                            mstore(0xce00, mulmod(mload(add(29568, 0xe0)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xce20, 0x95c0, 0x80)
                            mstore(0xcea0, mulmod(mload(add(29568, 0x100)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcec0, 0x9640, 0x80)
                            mstore(0xcf40, mulmod(mload(add(29568, 0x120)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xcf60, 0x96c0, 0x80)
                            mstore(0xcfe0, mulmod(mload(add(29568, 0x140)), solc_usr_x4_pow_3, solc_usr_r))
                            mcopy(0xd000, 0x9a40, 0x80)
                            mstore(0xd080, solc_usr_x4_pow_4)
                            mcopy(0xd0a0, 0x9ac0, 0x80)
                            mstore(0xd120, mulmod(mload(add(29568, 0x20)), solc_usr_x4_pow_4, solc_usr_r))
                            mcopy(0xd140, 0x9b40, 0x80)
                            mstore(0xd1c0, mulmod(mload(add(29568, 0x40)), solc_usr_x4_pow_4, solc_usr_r))
                            mcopy(0xd1e0, 0x9bc0, 0x80)
                            mstore(0xd260, mulmod(mload(add(29568, 0x60)), solc_usr_x4_pow_4, solc_usr_r))
                            mcopy(0xd280, 0x9c40, 0x80)
                            mstore(0xd300, mulmod(mload(add(29568, 0x80)), solc_usr_x4_pow_4, solc_usr_r))
                            mcopy(0xd320, 27328, 0x80)
                            mstore(0xd3a0, solc_usr_x4_pow_5)
                            if solc_usr_success
                            {
                                solc_usr_success := staticcall(gas(), 0x0c, 0xa300, 0x30c0, 28288, 0x80)
                                solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                            }
                            mstore(28256, solc_usr_v)
                        }
                        {
                            mcopy(28416, 27456, 0x80)
                            mcopy(0x80, 10336, 0x80)
                            mstore(0x100, addmod(0, sub(solc_usr_r, mload(28256)), solc_usr_r))
                            if solc_usr_success
                            {
                                solc_usr_success := staticcall(gas(), 0x0c, 0x80, 0xa0, 0x80, 0x80)
                                solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                            }
                            mcopy(0x100, 28288, 0x80)
                            if solc_usr_success
                            {
                                solc_usr_success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                                solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                            }
                            mcopy(0x100, 27456, 0x80)
                            mstore(0x180, mload(27264))
                            if solc_usr_success
                            {
                                solc_usr_success := staticcall(gas(), 0x0c, 0x100, 0xa0, 0x100, 0x80)
                                solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                            }
                            if solc_usr_success
                            {
                                solc_usr_success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                                solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                            }
                            mcopy(28544, 0x80, 0x80)
                        }
                    }
                    {
                        let solc_usr_batch_ptr := 0x0100
                        mstore(solc_usr_batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
                        mcopy(add(solc_usr_batch_ptr, 0x20), 28544, 0x80)
                        mcopy(add(solc_usr_batch_ptr, 0xa0), 28416, 0x80)
                        mcopy(add(solc_usr_batch_ptr, 0x0120), 27712, 0x80)
                        mcopy(add(solc_usr_batch_ptr, 0x01a0), 27584, 0x80)
                        let solc_usr_acc_pair_alpha := mod(keccak256(solc_usr_batch_ptr, 0x0220), solc_usr_r)
                        if iszero(solc_usr_acc_pair_alpha) { solc_usr_acc_pair_alpha := 1 }
                        mcopy(solc_usr_batch_ptr, 27712, 0x80)
                        mstore(add(solc_usr_batch_ptr, 0x80), solc_usr_acc_pair_alpha)
                        if solc_usr_success
                        {
                            solc_usr_success := staticcall(gas(), 0x0c, solc_usr_batch_ptr, 0xa0, solc_usr_batch_ptr, 0x80)
                            solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                        }
                        mcopy(add(solc_usr_batch_ptr, 0x80), 28544, 0x80)
                        if solc_usr_success
                        {
                            solc_usr_success := staticcall(gas(), 0x0b, solc_usr_batch_ptr, 0x0100, 28544, 0x80)
                            solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                        }
                        mcopy(solc_usr_batch_ptr, 27584, 0x80)
                        mstore(add(solc_usr_batch_ptr, 0x80), solc_usr_acc_pair_alpha)
                        if solc_usr_success
                        {
                            solc_usr_success := staticcall(gas(), 0x0c, solc_usr_batch_ptr, 0xa0, solc_usr_batch_ptr, 0x80)
                            solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                        }
                        mcopy(add(solc_usr_batch_ptr, 0x80), 28416, 0x80)
                        if solc_usr_success
                        {
                            solc_usr_success := staticcall(gas(), 0x0b, solc_usr_batch_ptr, 0x0100, 28416, 0x80)
                            solc_usr_success := and(solc_usr_success, eq(returndatasize(), 0x80))
                        }
                    }
                    if iszero(solc_usr_success) { revert(0, 0) }
                    solc_usr_success := solc_usr_ec_pairing(solc_usr_success, 28544, 28416)
                    mstore(128, 1)
                    return(128, 0x20)
                }

            }
            

        }

        data ".metadata" hex"a164736f6c634300081e000a"
    }

}

/-- The runtime sub-object name solc gives `Halo2Verifier`. Surface.irRuntime
    (Lowering/Surface.lean:467) resolves it through S.runtimeName ir.name, so this
    is the string a Surface must return for the imported object to be the one a run
    talks about. -/
def verifierRuntimeName : String := "Halo2Verifier_292_deployed"

/-- The deployed runtime sub-object of verifierIr, as an object: it carries the .metadata
    data segment the creation object refers to by name. The none arm is unreachable and
    irShape_ok is what says so. -/
def verifierRuntimeObject : Object EVM.Op :=
  match verifierIr.subObject verifierRuntimeName with
  | some o => o
  | none => verifierIr

/-- The deployed runtime block: the block RunContractIR runs. -/
def verifierRuntime : Block EVM.Op := Object.codeBlock verifierRuntimeObject

/-- The creation object code block: where setimmutable lives. The deployed side
    only ever reads immutables, through loadimmutable. -/
def verifierCreation : Block EVM.Op := Object.codeBlock verifierIr

/-- The ir artifact of proofs/solidity-verifier/deployments/sepolia/moonlight-wrap/Halo2VerifyingKey.sol, contract Halo2VerifyingKey: solc textual
    via-IR, imported verbatim as a yulObject% quotation except for the two
    alpha-renames documented in this file header. Top-level object "Halo2VerifyingKey_302", runtime sub-object
    "Halo2VerifyingKey_302_deployed".

    sha256 of the committed artifact: af3ccbdbf57bae598ef99dc383b5684ae70bc632db4ab39c241c349eae6724bf
    FNV-1a-64: 7388129883150509039   bytes: 64329   lines: 604   dollar signs: 537 -/

def vkIr : Object EVM.Op := yulObject% 

object "Halo2VerifyingKey_302" {
    code {
        
        mstore(64, 128)
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_Halo2VerifyingKey_302()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("Halo2VerifyingKey_302_deployed"), datasize("Halo2VerifyingKey_302_deployed"))

        return(_1, datasize("Halo2VerifyingKey_302_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        
        
        function constructor_Halo2VerifyingKey_302() {

            

            
            {
                let solc_usr_runtime := 0x80
                let solc_usr_payload := add(solc_usr_runtime, 0x01)
                mstore8(solc_usr_runtime, 0xfe)
                mstore(add(solc_usr_payload, 0x0000), 0x56c0824fcff237dd8dc7b15f527346d9e1647d191815acb142500b0293e84f66)
                mstore(add(solc_usr_payload, 0x0020), 0x0000000000000000000000000000000000000000000000000000000000000013)
                mstore(add(solc_usr_payload, 0x0040), 0x0000000000000000000000000000000000000000000000000000000000000014)
                mstore(add(solc_usr_payload, 0x0060), 0x73eda0144f284aae5b6554d46c21576b363d4ec725be2bff1a400fff00001001)
                mstore(add(solc_usr_payload, 0x0080), 0x03e1c54bcb947035a57a6e07cb98de4a2f69e02d265e09d9fece7e0e39898d4b)
                mstore(add(solc_usr_payload, 0x00a0), 0x6c39442eade0092768ac033fa6f608750624a1bb17dbc026ef97c3573a28fc8c)
                mstore(add(solc_usr_payload, 0x00c0), 0x2a0ccbaa0613f093f2bb6e97859513f0b613d8587eaa92db9e5604b8d6b68d45)
                mstore(add(solc_usr_payload, 0x00e0), 0x0000000000000000000000000000000000000000000000000000000000000001)
                mstore(add(solc_usr_payload, 0x0100), 0x000000000000000000000000000000000000000000000000000000000000000b)
                mstore(add(solc_usr_payload, 0x0120), 0x0000000000000000000000000000000000000000000000000000000000000007)
                mstore(add(solc_usr_payload, 0x0140), 0x0000000000000000000000000000000000000000000000000000000000000038)
                mstore(add(solc_usr_payload, 0x0160), 0x0000000000000000000000000000000017f1d3a73197d7942695638c4fa9ac0f)
                mstore(add(solc_usr_payload, 0x0180), 0xc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
                mstore(add(solc_usr_payload, 0x01a0), 0x0000000000000000000000000000000008b3f481e3aaa0f1a09e30ed741d8ae4)
                mstore(add(solc_usr_payload, 0x01c0), 0xfcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
                mstore(add(solc_usr_payload, 0x01e0), 0x00000000000000000000000000000000024aa2b2f08f0a91260805272dc51051)
                mstore(add(solc_usr_payload, 0x0200), 0xc6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8)
                mstore(add(solc_usr_payload, 0x0220), 0x0000000000000000000000000000000013e02b6052719f607dacd3a088274f65)
                mstore(add(solc_usr_payload, 0x0240), 0x596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
                mstore(add(solc_usr_payload, 0x0260), 0x000000000000000000000000000000000ce5d527727d6e118cc9cdc6da2e351a)
                mstore(add(solc_usr_payload, 0x0280), 0xadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801)
                mstore(add(solc_usr_payload, 0x02a0), 0x000000000000000000000000000000000606c4a02ea734cc32acd2b02bc28b99)
                mstore(add(solc_usr_payload, 0x02c0), 0xcb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
                mstore(add(solc_usr_payload, 0x02e0), 0x000000000000000000000000000000000632aaf712568f19c297802268a7ad9d)
                mstore(add(solc_usr_payload, 0x0300), 0xceea6ef7ab6f75a7d26781c8e90c7432bc5e99dcc219ba64010f3052123983ab)
                mstore(add(solc_usr_payload, 0x0320), 0x00000000000000000000000000000000191ff4920e077a2f8cb3969ba8f05bc2)
                mstore(add(solc_usr_payload, 0x0340), 0xaa9da8c95d640b1e051be7cf344ee7f01996df2568bf0e7ccd9eb70978820045)
                mstore(add(solc_usr_payload, 0x0360), 0x0000000000000000000000000000000005f434ebf45460a864ad5b17497c7903)
                mstore(add(solc_usr_payload, 0x0380), 0x71820c70c83aa186029536d22dff54373251152c28bc43269f95281eba1b012e)
                mstore(add(solc_usr_payload, 0x03a0), 0x0000000000000000000000000000000004d1c747141bcac15e77e3e1d3853254)
                mstore(add(solc_usr_payload, 0x03c0), 0xc8687afdad35345a04f79d9c2759007f6640676eb44aee7011ce5ad80744bb23)
                mstore(add(solc_usr_payload, 0x03e0), 0x0000000000000000000000000000000000000000000000000000000000000001)
                mstore(add(solc_usr_payload, 0x0400), 0x00bbe1fbe9ef1e2d62490b03a82bf9ef10f5e9b2323033669cf6c50481f63e05)
                mstore(add(solc_usr_payload, 0x0420), 0x0000000000000000000000000000000000000000000000000100000000000000)
                mstore(add(solc_usr_payload, 0x0440), 0x0000000000000000000000000000000000010000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0460), 0x0000000000000000000000000000000000000000000000000000000400000000)
                mstore(add(solc_usr_payload, 0x0480), 0x0000000000000000000000000000000000000000040000000000000000000000)
                mstore(add(solc_usr_payload, 0x04a0), 0x0000000000000000000000000000000000000000000000000000000000001000)
                mstore(add(solc_usr_payload, 0x04c0), 0x0000000000000000000000000000000000000000000000100000000000000000)
                mstore(add(solc_usr_payload, 0x04e0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000)
                mstore(add(solc_usr_payload, 0x0500), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefeffffff00000001)
                mstore(add(solc_usr_payload, 0x0520), 0x73eda753299d7d483339d80809a1d80553bca402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x0540), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffb00000001)
                mstore(add(solc_usr_payload, 0x0560), 0x73eda753299d7d483339d80809a1d80553bda402fbfe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x0580), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffefffff001)
                mstore(add(solc_usr_payload, 0x05a0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5beeffffffff00000001)
                mstore(add(solc_usr_payload, 0x05c0), 0x00000000000000000000000000000010ff0726c5de281020ad8016cf6f691213)
                mstore(add(solc_usr_payload, 0x05e0), 0x0000000000000000000000000000002c64068790f917282347187665718b04c8)
                mstore(add(solc_usr_payload, 0x0600), 0x00000000000000000000000000000027241bb5338dce8a77499428839473bf3a)
                mstore(add(solc_usr_payload, 0x0620), 0x0000000000000000000000000000002b7c4a26a1c7ae6fc4b499d04e4a463c4b)
                mstore(add(solc_usr_payload, 0x0640), 0x000000000000000000000000000000274bc40fcf526be95333a8c22c79465298)
                mstore(add(solc_usr_payload, 0x0660), 0x0000000000000000000000000000002a5ee6db49930276e2939d1c43ac82f744)
                mstore(add(solc_usr_payload, 0x0680), 0x73eda753299d7d483339d80809a1d7edd77e26c51c38afb5debf8afa00c15cc3)
                mstore(add(solc_usr_payload, 0x06a0), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000002)
                mstore(add(solc_usr_payload, 0x06c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe53ebc627fffef6280001)
                mstore(add(solc_usr_payload, 0x06e0), 0x0000000000000000000001000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0700), 0x0000000100000000000000000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0720), 0x6bc66e553973f396854f5626172ba135587d41e37a68209402355093fdcaaf6c)
                mstore(add(solc_usr_payload, 0x0740), 0x63f31e3f446953960c9d6964474300df43ab29179970f642a28e39d6c883c74b)
                mstore(add(solc_usr_payload, 0x0760), 0x73eda753299d7d483339d70809a1d80553bda402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x0780), 0x73eda752299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x07a0), 0x082738fdf02989b1adea81e1f27636cffb40621f85963b6afdcaaf6b02355095)
                mstore(add(solc_usr_payload, 0x07c0), 0x0ffa8913e53429b2269c6ea3c25ed72610127aeb668d65bc5d71c628377c38b6)
                mstore(add(solc_usr_payload, 0x07e0), 0x01ec1c0519185dfe86132d479c76d0786e1e037d0b05ca47648a1c5d29492c9b)
                mstore(add(solc_usr_payload, 0x0800), 0x1e179025ca2470882b34e63940ccbd7ad9090bf414d43b696e093b5a8782528f)
                mstore(add(solc_usr_payload, 0x0820), 0x4298bfee9a84c8ef8e83702075cb1abeb576f146636342e3db9ea6b0a4adf29d)
                mstore(add(solc_usr_payload, 0x0840), 0x3c83b078e9abed278d042acc8f3bd21e228716f04be96af8025da860e2d1bba9)
                mstore(add(solc_usr_payload, 0x0860), 0x427868260f487d1ef07edaadf37f5dbe705bd1318290f2577ae756b009c24f11)
                mstore(add(solc_usr_payload, 0x0880), 0x03020e6a35e595abd22838beeadc45cfcb0545d85ca0ab2c59d44c203fac84a7)
                mstore(add(solc_usr_payload, 0x08a0), 0x000000000000000000000000000000000000000000000000d201000000010000)
                mstore(add(solc_usr_payload, 0x08c0), 0x0000000100001b7c3f8d3fe3c5b448f1bdeb2ae34698b72d6ce966fc208c05ed)
                mstore(add(solc_usr_payload, 0x08e0), 0x73eda753299d7d483339d80809a1d7fd4057a4c12f26d1c1778e3360a6820001)
                mstore(add(solc_usr_payload, 0x0900), 0x057797fa7060856f215654ff11006fe0acf6a437e9477bf6f782dfac86f2cf75)
                mstore(add(solc_usr_payload, 0x0920), 0x0000000000000000000000000000000000000000000000000000000000000002)
                mstore(add(solc_usr_payload, 0x0940), 0x0000000000000000000000000000000000000000000000000200000000000000)
                mstore(add(solc_usr_payload, 0x0960), 0x0000000000000000000000000000000000020000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0980), 0x73eda753299d7d483339d80809a1d7e13511a4044eaa5bff4600ffff00005556)
                mstore(add(solc_usr_payload, 0x09a0), 0x73eda753299d7d483339d80809a1d7c553bda402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x09c0), 0x73eda753299d7d483339d80809a1d7d340dd972492de594de627fffefcb80349)
                mstore(add(solc_usr_payload, 0x09e0), 0x73eda753299d7d483339d80809a1d7dbdc391ab4d8ac003bbd48021b82456c9b)
                mstore(add(solc_usr_payload, 0x0a00), 0x73eda753299d7d483339d80809a1d7d1448ee5caf5eefcffbc9fabc57759e23f)
                mstore(add(solc_usr_payload, 0x0a20), 0x73eda753299d7d483339d80809a1d80418c74cc18bb28443d3978d1fd47ffce1)
                mstore(add(solc_usr_payload, 0x0a40), 0x0000000000000000000000000000006425c019bcda40056233b00000068ff970)
                mstore(add(solc_usr_payload, 0x0a60), 0x00000000000000000000000000000052ef09129c4ea4b786856ffbc6fb7526cc)
                mstore(add(solc_usr_payload, 0x0a80), 0x73eda753299d7d483339d80809a1d7d89a085d30fc8a7106a170ac2377c34ab9)
                mstore(add(solc_usr_payload, 0x0aa0), 0x73eda753299d7d483339d80809a1d7f8ce65bb936f2d836012914aca65f077e1)
                mstore(add(solc_usr_payload, 0x0ac0), 0x000000000000000000000000000000681e5d7c70141ebdfe86c0a873114c3b84)
                mstore(add(solc_usr_payload, 0x0ae0), 0x000000000000000000000000000000297784894e27525bc342b7fde37dba9366)
                mstore(add(solc_usr_payload, 0x0b00), 0x0000000000000000000000000000000275ecae82e897af7658d0e5be57000640)
                mstore(add(solc_usr_payload, 0x0b20), 0x000000000000000000000000000000013af65741744bd7bb2c6872df2b800320)
                mstore(add(solc_usr_payload, 0x0b40), 0x00000000000000000000000000000059736a8da406e7d5f0bd1ea7b710796a90)
                mstore(add(solc_usr_payload, 0x0b60), 0x0000000000000000000000000000000c8557e86f90d0d89eed6eb5349a0f8820)
                mstore(add(solc_usr_payload, 0x0b80), 0x0453ae02a5f228d8f956b5eab4fc92bbeea5eb26b6ae4b42b4fdfcfdf026aa22)
                mstore(add(solc_usr_payload, 0x0ba0), 0x0000000000000000000000000000000000000000000000000000000800000000)
                mstore(add(solc_usr_payload, 0x0bc0), 0x0000000000000000000000000000000000000000080000000000000000000000)
                mstore(add(solc_usr_payload, 0x0be0), 0x0000000000000000000000000000000000000000000000000000000000002000)
                mstore(add(solc_usr_payload, 0x0c00), 0x0000000000000000000000000000000000000000000000200000000000000000)
                mstore(add(solc_usr_payload, 0x0c20), 0x73eda753299d7d483339d80809a1d7f454b67d3d21d64bde527fe92f9096edee)
                mstore(add(solc_usr_payload, 0x0c40), 0x73eda753299d7d483339d80809a1d7d8efb71c7206e733dbb8e789998e74fb39)
                mstore(add(solc_usr_payload, 0x0c60), 0x73eda753299d7d483339d80809a1d7de2fa1eecf722fd187b66bd77b6b8c40c7)
                mstore(add(solc_usr_payload, 0x0c80), 0x73eda753299d7d483339d80809a1d7d9d7737d61384fec3a4b662fb0b5b9c3b6)
                mstore(add(solc_usr_payload, 0x0ca0), 0x73eda753299d7d483339d80809a1d7de07f99433ad9272abcc573dd286b9ad69)
                mstore(add(solc_usr_payload, 0x0cc0), 0x73eda753299d7d483339d80809a1d7daf4d6c8b96cfbe51c6c62e3bb537d08bd)
                mstore(add(solc_usr_payload, 0x0ce0), 0x00000000000000000000000000000021fe0e4d8bbc5020415b002d9eded22426)
                mstore(add(solc_usr_payload, 0x0d00), 0x00000000000000000000000000000058c80d0f21f22e50468e30eccae3160990)
                mstore(add(solc_usr_payload, 0x0d20), 0x0000000000000000000000000000004e48376a671b9d14ee9328510728e77e74)
                mstore(add(solc_usr_payload, 0x0d40), 0x00000000000000000000000000000056f8944d438f5cdf896933a09c948c7896)
                mstore(add(solc_usr_payload, 0x0d60), 0x0000000000000000000000000000004e97881f9ea4d7d2a667518458f28ca530)
                mstore(add(solc_usr_payload, 0x0d80), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb9194fffd)
                mstore(add(solc_usr_payload, 0x0da0), 0x0000000000000000000002000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0dc0), 0x0000000200000000000000000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x0de0), 0x639f3557494a69e4d764d44424b56a655d3cdfc3f4d1e529046aa128fb955ed7)
                mstore(add(solc_usr_payload, 0x0e00), 0x53f8952b5f3529e3e600fac084e429b93398ae2c32e39086451c73ae91078e95)
                mstore(add(solc_usr_payload, 0x0e20), 0x72018b4e10851f49ad26aac06d2b078ce59fa085f4f891b79b75e3a1d6b6d366)
                mstore(add(solc_usr_payload, 0x0e40), 0x55d6172d5f790cc00804f1cec8d51a8a7ab4980eeb2a209591f6c4a4787dad72)
                mstore(add(solc_usr_payload, 0x0e60), 0x3154e7648f18b458a4b667e793d6bd469e46b2bc9c9b191b2461594e5b520d64)
                mstore(add(solc_usr_payload, 0x0e80), 0x3769f6da3ff19020a635ad3b7a6605e731368d12b414f106fda2579e1d2e4458)
                mstore(add(solc_usr_payload, 0x0ea0), 0x31753f2d1a55002942bafd5a16227a46e361d2d17d6d69a78518a94ef63db0f0)
                mstore(add(solc_usr_payload, 0x0ec0), 0x70eb98e8f3b7e79c61119f491ec5923588b85e2aa35db0d2a62bb3dec0537b5a)
                mstore(add(solc_usr_payload, 0x0ee0), 0x03d8380a3230bbfd0c265a8f38eda0f0dc3c06fa160b948ec91438ba52925936)
                mstore(add(solc_usr_payload, 0x0f00), 0x3c2f204b9448e1105669cc7281997af5b21217e829a876d2dc1276b50f04a51e)
                mstore(add(solc_usr_payload, 0x0f20), 0x1143d88a0b6c1496e9cd0838e1f45d7817303e89c6c829c8b73d4d62495be539)
                mstore(add(solc_usr_payload, 0x0f40), 0x0519b99ea9ba5d06e6ce7d9114d5cc36f15089dd97d479f104bb50c2c5a37751)
                mstore(add(solc_usr_payload, 0x0f60), 0x110328f8f4f37cf5adc3dd53dd5ce3778cf9fe60052388aff5cead6113849e21)
                mstore(add(solc_usr_payload, 0x0f80), 0x057797fa7060856f215655ff11006fee9a1697597c277945ddaadfac83aad2c0)
                mstore(add(solc_usr_payload, 0x0fa0), 0x0000000000000000000000000000003212e00cde6d2002b119d800000347fcb8)
                mstore(add(solc_usr_payload, 0x0fc0), 0x000000000000000000000000000000340f2ebe380a0f5eff4360543988a61dc2)
                mstore(add(solc_usr_payload, 0x0fe0), 0x0000000000000000000000000000002cb9b546d20373eaf85e8f53db883cb548)
                mstore(add(solc_usr_payload, 0x1000), 0x0453ae02a5f228d8f956b6eab50092aaff9ec460d8863b22077de62a80bd8812)
                mstore(add(solc_usr_payload, 0x1020), 0x73eda753299d7d4833351088b4af7508df8b737010b26601ef73fcbb87bd0000)
                mstore(add(solc_usr_payload, 0x1040), 0x0aef2ff4e0c10ade42aca9fe2200e00159ed486fd28ef7edef05bf590de59ef3)
                mstore(add(solc_usr_payload, 0x1060), 0x0000000000000000000000000000000000000000000000000000000000000006)
                mstore(add(solc_usr_payload, 0x1080), 0x0000000000000000000000000000000000000000000000000600000000000000)
                mstore(add(solc_usr_payload, 0x10a0), 0x0000000000000000000000000000000000060000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x10c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffffff)
                mstore(add(solc_usr_payload, 0x10e0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefdffffff00000001)
                mstore(add(solc_usr_payload, 0x1100), 0x73eda753299d7d483339d80809a1d80553bba402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x1120), 0x0000000000000000000000000000000000000000000000000000000000000003)
                mstore(add(solc_usr_payload, 0x1140), 0x0000000000000000000000000000000000030000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x1160), 0x0000000000000000000000000000012c71404d368ec010269b10000013afec50)
                mstore(add(solc_usr_payload, 0x1180), 0x000000000000000000000000000000f8cd1b37d4ebee2693904ff354f25f7464)
                mstore(add(solc_usr_payload, 0x11a0), 0x000000000000000000000000000001385b1875503c5c39fb9441f95933e4b28c)
                mstore(add(solc_usr_payload, 0x11c0), 0x0000000000000000000000000000007c668d9bea75f71349c827f9aa792fba32)
                mstore(add(solc_usr_payload, 0x11e0), 0x0000000000000000000000000000000761c60b88b9c70e630a72b13b050012c0)
                mstore(add(solc_usr_payload, 0x1200), 0x73eda753299d7d483339d80809a1d7a12dfd8a4625be569ccc4ffffef9700691)
                mstore(add(solc_usr_payload, 0x1220), 0x73eda753299d7d483339d80809a1d7b264b49166b159a4787a900438048ad935)
                mstore(add(solc_usr_payload, 0x1240), 0x00000000000000000000000000000003b0e305c45ce387318539589d82800960)
                mstore(add(solc_usr_payload, 0x1260), 0x0000000000000000000000000000010c5a3fa8ec14b781d2375bf725316c3fb0)
                mstore(add(solc_usr_payload, 0x1280), 0x000000000000000000000000000000259007b94eb27289dcc84c1f9dce2e9860)
                mstore(add(solc_usr_payload, 0x12a0), 0x73eda753299d7d483339d80809a1d79d35602792ebdf9e00793f578beeb3c47d)
                mstore(add(solc_usr_payload, 0x12c0), 0x73eda753299d7d483339d80809a1d802ddd0f5801766ac88a72f1a40a8fff9c1)
                mstore(add(solc_usr_payload, 0x12e0), 0x73eda753299d7d483339d80809a1d7abe053165ef916860e42e15847ef869571)
                mstore(add(solc_usr_payload, 0x1300), 0x73eda753299d7d483339d80809a1d7ec490dd323de5caac125229595cbe0efc1)
                mstore(add(solc_usr_payload, 0x1320), 0x08a75c054be451b1f2ad6bd569f92577dd4bd64d6d5c968569fbf9fbe04d544d)
                mstore(add(solc_usr_payload, 0x1340), 0x0000000000000000000000000000000000000000000000000000001800000000)
                mstore(add(solc_usr_payload, 0x1360), 0x0000000000000000000000000000000000000000180000000000000000000000)
                mstore(add(solc_usr_payload, 0x1380), 0x0000000000000000000000000000000000000000000000000000000000006000)
                mstore(add(solc_usr_payload, 0x13a0), 0x0000000000000000000000000000000000000000000000600000000000000000)
                mstore(add(solc_usr_payload, 0x13c0), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffff700000001)
                mstore(add(solc_usr_payload, 0x13e0), 0x73eda753299d7d483339d80809a1d80553bda402f7fe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x1400), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfefffffffeffffe001)
                mstore(add(solc_usr_payload, 0x1420), 0x73eda753299d7d483339d80809a1d80553bda402fffe5bdeffffffff00000001)
                mstore(add(solc_usr_payload, 0x1440), 0x73eda753299d7d483339d80809a1d7e355af567743ae3bbda4ffd260212ddbdb)
                mstore(add(solc_usr_payload, 0x1460), 0x73eda753299d7d483339d80809a1d7ac8bb094e10dd00bb871cf13341ce9f671)
                mstore(add(solc_usr_payload, 0x1480), 0x73eda753299d7d483339d80809a1d7b70b86399be46147106cd7aef7d718818d)
                mstore(add(solc_usr_payload, 0x14a0), 0x73eda753299d7d483339d80809a1d7ae5b2956bf70a17c7596cc5f626b73876b)
                mstore(add(solc_usr_payload, 0x14c0), 0x73eda753299d7d483339d80809a1d7b6bc3584645b26895898ae7ba60d735ad1)
                mstore(add(solc_usr_payload, 0x14e0), 0x73eda753299d7d483339d80809a1d7b095efed6fd9f96e39d8c5c777a6fa1179)
                mstore(add(solc_usr_payload, 0x1500), 0x00000000000000000000000000000065fa2ae8a334f060c4110088dc9c766c72)
                mstore(add(solc_usr_payload, 0x1520), 0x00000000000000000000000000000000000000000c0000000000000000000000)
                mstore(add(solc_usr_payload, 0x1540), 0x0000000000000000000000000000010a58272d65d68af0d3aa92c660a9421cb0)
                mstore(add(solc_usr_payload, 0x1560), 0x0000000000000000000000000000000000000000000000300000000000000000)
                mstore(add(solc_usr_payload, 0x1580), 0x000000000000000000000000000000ead8a63f3552d73ecbb978f3157ab67b5c)
                mstore(add(solc_usr_payload, 0x15a0), 0x000000000000000000000000000000852c1396b2eb457869d549633054a10e58)
                mstore(add(solc_usr_payload, 0x15c0), 0x00000000000000000000000000000104e9bce7caae169e9c3b9ae1d5bda569c2)
                mstore(add(solc_usr_payload, 0x15e0), 0x0000000000000000000000000000008274de73e5570b4f4e1dcd70eaded2b4e1)
                mstore(add(solc_usr_payload, 0x1600), 0x000000000000000000000000000000ebc6985edbee8777f335f48d0ad7a5ef90)
                mstore(add(solc_usr_payload, 0x1620), 0x0000000000000000000000000000007f1cb491dcb90764a7bad754cb0588e5cc)
                mstore(add(solc_usr_payload, 0x1640), 0x73eda753299d7d48333049095fbd120c6b5942dd2166802b5297f978232a0002)
                mstore(add(solc_usr_payload, 0x1660), 0x0000000000000000000006000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x1680), 0x0000000600000000000000000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x16a0), 0x4302515f88a4431e1fbaccbc5adc8f25703b5745de78f77d0d3fe37cf2c01c83)
                mstore(add(solc_usr_payload, 0x16c0), 0x140e70dbca64831b4b8f40317b68cd20f34ec27e98adf994cf555b0db316abbd)
                mstore(add(solc_usr_payload, 0x16e0), 0x73eda753299d7d483339d60809a1d80553bda402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x1700), 0x73eda751299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001)
                mstore(add(solc_usr_payload, 0x1720), 0x104e71fbe05313635bd503c3e4ec6d9ff680c43f0b2c76d5fb955ed6046aa12a)
                mstore(add(solc_usr_payload, 0x1740), 0x1ff51227ca6853644d38dd4784bdae4c2024f5d6cd1acb78bae38c506ef8716c)
                mstore(add(solc_usr_payload, 0x1760), 0x70156f48f76cc14b27137d78d0b4371477819d08e9f2c77036ebc744ad6da6cb)
                mstore(add(solc_usr_payload, 0x1780), 0x37be870795549c37dcd00b9588085d0fa1ab8c1ad655e52c23ed8949f0fb5ae3)
                mstore(add(solc_usr_payload, 0x17a0), 0x62a9cec91e3168b1496ccfcf27ad7a8d3c8d65793936323648c2b29cb6a41ac8)
                mstore(add(solc_usr_payload, 0x17c0), 0x6ed3edb47fe320414c6b5a76f4cc0bce626d1a256829e20dfb44af3c3a5c88b0)
                mstore(add(solc_usr_payload, 0x17e0), 0x62ea7e5a34aa00528575fab42c44f48dc6c3a5a2fadad34f0a31529dec7b61e0)
                mstore(add(solc_usr_payload, 0x1800), 0x6de98a7ebdd251f08ee9668a33e94c65bdb3185246bd05a64c5767be80a6f6b3)
                mstore(add(solc_usr_payload, 0x1820), 0x0b88a81e969233f724730fadaac8e2d294b414ee4222bdac5b3caa2ef7b70ba2)
                mstore(add(solc_usr_payload, 0x1840), 0x0000000300000000000000000000000000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x1860), 0x409fb98f933d25e8d0038d4f7b2a98dbc278a3b57cfb0879943764202d0def59)
                mstore(add(solc_usr_payload, 0x1880), 0x43fe0c177a010031bf648c1cc285529323863340cc562ac9e7aaad86598b55df)
                mstore(add(solc_usr_payload, 0x18a0), 0x33cb899e22443dc4bd6718aaa5dd18684590bb9d54587d5a25b7e826dc13afab)
                mstore(add(solc_usr_payload, 0x18c0), 0x5a46b0715e6d5198819eb2abc26638708b1b23dc3e7cb23c4a1bb20f9686f7ad)
                mstore(add(solc_usr_payload, 0x18e0), 0x0f4d2cdbfd2f1714b46b78b33e8164a4d3f19d98c77d6dd30e31f24850ea65f3)
                mstore(add(solc_usr_payload, 0x1900), 0x419d6a1793664a2e73d2a85da4119e5513d7a0cde3bde4e90718f923a87532fa)
                mstore(add(solc_usr_payload, 0x1920), 0x33097aeadeda76e1094b97fb9816aa66a6edfb200f6a9a0fe16c08233a8dda63)
                mstore(add(solc_usr_payload, 0x1940), 0x09062b3ea1b0c1037678aa3cc094d16f610fd18915e201850d7ce460bf058df5)
                mstore(add(solc_usr_payload, 0x1960), 0x0456a29a706afacf2158850711006fe0acf6a437e9477bf6f782dfac86f2cf7b)
                mstore(add(solc_usr_payload, 0x1980), 0x0397cc06bc030aab970dabe70cd498bbeea8daaea65607bb6a872125fec74a10)
                mstore(add(solc_usr_payload, 0x19a0), 0x73eda753299d7d4833351088b4af7508df8b737010b26e15294bfcbb91950003)
                mstore(add(solc_usr_payload, 0x19c0), 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140)
                mstore(add(solc_usr_payload, 0x19e0), 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a)
                mstore(add(solc_usr_payload, 0x1a00), 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db)
                mstore(add(solc_usr_payload, 0x1a20), 0x058560108a8005860008060d000b0200011b0000210201030700020000852002)
                mstore(add(solc_usr_payload, 0x1a40), 0x85400385600485800585a00085c00285e0038600068620078640088660098680)
                mstore(add(solc_usr_payload, 0x1a60), 0x0a86a00b86c00c86e00d87000e87200487400587600687800787a085200085c0)
                mstore(add(solc_usr_payload, 0x1a80), 0x0285e00386000487400587600687800787a085400285c00385e0048600058740)
                mstore(add(solc_usr_payload, 0x1aa0), 0x0687600787800f87a085600385c00485e00586000687400787600f87801087a0)
                mstore(add(solc_usr_payload, 0x1ac0), 0x85800485c00585e00686000787400f87601087801187a085a00585c00685e007)
                mstore(add(solc_usr_payload, 0x1ae0), 0x86000f87401087601187801287a086200685c00785e00f860010874011876012)
                mstore(add(solc_usr_payload, 0x1b00), 0x87801387a086400785c00f85e01086001187401287601387801487a01587c016)
                mstore(add(solc_usr_payload, 0x1b20), 0x88000b03000121021703070001000085200285400385601885801985a00085c0)
                mstore(add(solc_usr_payload, 0x1b40), 0x0285e00386001a86201b86400886600986800a86a01c86c01d86e01e87001f87)
                mstore(add(solc_usr_payload, 0x1b60), 0x201887401987601a87801b87a085200085c00285e00386001887401987601a87)
                mstore(add(solc_usr_payload, 0x1b80), 0x801b87a085400285c00385e01886001987401a87601b87802087a085600385c0)
                mstore(add(solc_usr_payload, 0x1ba0), 0x1885e01986001a87401b87602087802187a085801885c01985e01a86001b8740)
                mstore(add(solc_usr_payload, 0x1bc0), 0x2087602187802287a085a01985c01a85e01b86002087402187602287802387a0)
                mstore(add(solc_usr_payload, 0x1be0), 0x86201a85c01b85e02086002187402287602387802487a086401b85c02085e021)
                mstore(add(solc_usr_payload, 0x1c00), 0x86002287402387602487802587a02687c00b0300011b00012102270100000900)
                mstore(add(solc_usr_payload, 0x1c20), 0x0686200786400886600986800a86a00b86c00c86e00085200285400385600485)
                mstore(add(solc_usr_payload, 0x1c40), 0x800585a00d87000e87201587c01688000b04000121022801000008001a86201b)
                mstore(add(solc_usr_payload, 0x1c60), 0x86400886600986800a86a01c86c01d86e00085200285400385601885801985a0)
                mstore(add(solc_usr_payload, 0x1c80), 0x1e87001f87202687c00b04000121038820290000000b2b0885200985400a8560)
                mstore(add(solc_usr_payload, 0x1ca0), 0x2a85c02b85e02c86000886600986800a86a02d87c02e87e00885208660098520)
                mstore(add(solc_usr_payload, 0x1cc0), 0x86800a852086a009854086600a854086802f854087200a856086602f85608700)
                mstore(add(solc_usr_payload, 0x1ce0), 0x30856087202f858086e0308580870031858087202f85a086c03085a086e03185)
                mstore(add(solc_usr_payload, 0x1d00), 0xa087003285a087200085c085c02b85c085e02c85c086000385e085e03385e087)
                mstore(add(solc_usr_payload, 0x1d20), 0xa0338600878034860087a02f862086a030862086c031862086e0328620870035)
                mstore(add(solc_usr_payload, 0x1d40), 0x862087202f8640868030864086a031864086c032864086e03586408700368640)
                mstore(add(solc_usr_payload, 0x1d60), 0x87203387408760348740878037874087a03887608760378760878039876087a0)
                mstore(add(solc_usr_payload, 0x1d80), 0x3a878087803b878087a03c87a087a00d000b050000210388203d030800021508)
                mstore(add(solc_usr_payload, 0x1da0), 0x85200985400a85600b85800c85a02a85c02b85e02c86000d86200e8640088660)
                mstore(add(solc_usr_payload, 0x1dc0), 0x0986800a86a00b86c00c86e00d87000e87203e87403f87604087804187a08520)
                mstore(add(solc_usr_payload, 0x1de0), 0x0886600986800a86a00b86c00c86e00d87000e872085400986600a86800b86a0)
                mstore(add(solc_usr_payload, 0x1e00), 0x0c86c00d86e00e870042872085600a86600b86800c86a00d86c00e86e0428700)
                mstore(add(solc_usr_payload, 0x1e20), 0x43872085800b86600c86800d86a00e86c04286e043870044872085a00c86600d)
                mstore(add(solc_usr_payload, 0x1e40), 0x86800e86a04286c04386e044870045872085c00085c02b85e02c86003e87403f)
                mstore(add(solc_usr_payload, 0x1e60), 0x87604087804187a086200d86600e86804286a04386c04486e045870046872086)
                mstore(add(solc_usr_payload, 0x1e80), 0x400e86604286804386a04486c04586e04687004787201587c01688000385e085)
                mstore(add(solc_usr_payload, 0x1ea0), 0xe03e85e086003f85e087404085e087604185e087804885e087a0058600860040)
                mstore(add(solc_usr_payload, 0x1ec0), 0x860087404186008760488600878049860087a007874087404887408760498740)
                mstore(add(solc_usr_payload, 0x1ee0), 0x87804a874087a010876087604a876087804b876087a012878087804c878087a0)
                mstore(add(solc_usr_payload, 0x1f00), 0x1487a087a00d000b050001210388204d03080001150885200985400a85601c85)
                mstore(add(solc_usr_payload, 0x1f20), 0x801d85a02a85c02b85e02c86001e86201f86400886600986800a86a01c86c01d)
                mstore(add(solc_usr_payload, 0x1f40), 0x86e01e87001f87204e87404f87605087805187a085200886600986800a86a01c)
                mstore(add(solc_usr_payload, 0x1f60), 0x86c01d86e01e87001f872085400986600a86801c86a01d86c01e86e01f870052)
                mstore(add(solc_usr_payload, 0x1f80), 0x872085600a86601c86801d86a01e86c01f86e052870053872085801c86601d86)
                mstore(add(solc_usr_payload, 0x1fa0), 0x801e86a01f86c05286e053870054872085a01d86601e86801f86a05286c05386)
                mstore(add(solc_usr_payload, 0x1fc0), 0xe054870055872085c00085c02b85e02c86004e87404f87605087805187a08620)
                mstore(add(solc_usr_payload, 0x1fe0), 0x1e86601f86805286a05386c05486e055870056872086401f86605286805386a0)
                mstore(add(solc_usr_payload, 0x2000), 0x5486c05586e05687005787202687c00385e085e04e85e086004f85e087405085)
                mstore(add(solc_usr_payload, 0x2020), 0xe087605185e087805885e087a019860086005086008740518600876058860087)
                mstore(add(solc_usr_payload, 0x2040), 0x8059860087a01b87408740588740876059874087805a874087a021876087605a)
                mstore(add(solc_usr_payload, 0x2060), 0x876087805b876087a023878087805c878087a02587a087a00d000b0500012103)
                mstore(add(solc_usr_payload, 0x2080), 0x88205d0000000c390885200985400a85602d87c02e87e0008820008840028860)
                mstore(add(solc_usr_payload, 0x20a0), 0x0388800889200989400a89600085c088400285c088600385c088800885c08920)
                mstore(add(solc_usr_payload, 0x20c0), 0x0985c089400a85c089600285e088400385e088605e85e089000985e089200a85)
                mstore(add(solc_usr_payload, 0x20e0), 0xe089402f85e089e003860088405e860088e038860089000a860089202f860089)
                mstore(add(solc_usr_payload, 0x2100), 0xc030860089e0008660882002868088200386a088205e874088c038874088e05f)
                mstore(add(solc_usr_payload, 0x2120), 0x874089002f874089a030874089c031874089e05e876088a038876088c05f8760)
                mstore(add(solc_usr_payload, 0x2140), 0x88e03a876089002f8760898030876089a031876089c032876089e05e87808880)
                mstore(add(solc_usr_payload, 0x2160), 0x38878088a05f878088c03a878088e060878089002f8780896030878089803187)
                mstore(add(solc_usr_payload, 0x2180), 0x8089a032878089c035878089e05e87a088603887a088805f87a088a03a87a088)
                mstore(add(solc_usr_payload, 0x21a0), 0xc06087a088e03c87a089002f87a089403087a089603187a089803287a089a035)
                mstore(add(solc_usr_payload, 0x21c0), 0x87a089c03687a089e00d000b0600002103882061020f000a0016880000882000)
                mstore(add(solc_usr_payload, 0x21e0), 0x88400288600388800488a00588c00688e00789000889200989400a89600b8980)
                mstore(add(solc_usr_payload, 0x2200), 0x0c89a088200086600286800386a00486c00586e006870007872088400085c002)
                mstore(add(solc_usr_payload, 0x2220), 0x85e00386000487400587600687800787a088600285c00385e004860005874006)
                mstore(add(solc_usr_payload, 0x2240), 0x87600787800f87a088800385c00485e00586000687400787600f87801087a088)
                mstore(add(solc_usr_payload, 0x2260), 0xa00485c00585e00686000787400f87601087801187a088c00585c00685e00786)
                mstore(add(solc_usr_payload, 0x2280), 0x000f87401087601187801287a088e00685c00785e00f86001087401187601287)
                mstore(add(solc_usr_payload, 0x22a0), 0x801387a089000785c00f85e01086001187401287601387801487a085c0088920)
                mstore(add(solc_usr_payload, 0x22c0), 0x0989400a89600b89800c89a00d89c00e89e085e00989200a89400b89600c8980)
                mstore(add(solc_usr_payload, 0x22e0), 0x0d89a00e89c04289e086000a89200b89400c89600d89800e89a04289c04389e0)
                mstore(add(solc_usr_payload, 0x2300), 0x87400b89200c89400d89600e89804289a04389c04489e087600c89200d89400e)
                mstore(add(solc_usr_payload, 0x2320), 0x89604289804389a04489c04589e087800d89200e89404289604389804489a045)
                mstore(add(solc_usr_payload, 0x2340), 0x89c04689e087a00e89204289404389604489804589a04689c04789e008852009)
                mstore(add(solc_usr_payload, 0x2360), 0x85400a85600b85800c85a00d86200e86401587c00d89c00e89e00d000b060001)
                mstore(add(solc_usr_payload, 0x2380), 0x2103882062020f0009000088200088400288600388801888a01988c01a88e01b)
                mstore(add(solc_usr_payload, 0x23a0), 0x89000889200989400a89601c89801d89a01e89c088200086600286800386a018)
                mstore(add(solc_usr_payload, 0x23c0), 0x86c01986e01a87001b872088400085c00285e00386001887401987601a87801b)
                mstore(add(solc_usr_payload, 0x23e0), 0x87a088600285c00385e01886001987401a87601b87802087a088800385c01885)
                mstore(add(solc_usr_payload, 0x2400), 0xe01986001a87401b87602087802187a088a01885c01985e01a86001b87402087)
                mstore(add(solc_usr_payload, 0x2420), 0x602187802287a088c01985c01a85e01b86002087402187602287802387a088e0)
                mstore(add(solc_usr_payload, 0x2440), 0x1a85c01b85e02086002187402287602387802487a089001b85c02085e0218600)
                mstore(add(solc_usr_payload, 0x2460), 0x2287402387602487802587a085c00889200989400a89601c89801d89a01e89c0)
                mstore(add(solc_usr_payload, 0x2480), 0x1f89e085e00989200a89401c89601d89801e89a01f89c05289e086000a89201c)
                mstore(add(solc_usr_payload, 0x24a0), 0x89401d89601e89801f89a05289c05389e087401c89201d89401e89601f898052)
                mstore(add(solc_usr_payload, 0x24c0), 0x89a05389c05489e087601d89201e89401f89605289805389a05489c05589e087)
                mstore(add(solc_usr_payload, 0x24e0), 0x801e89201f89405289605389805489a05589c05689e087a01f89205289405389)
                mstore(add(solc_usr_payload, 0x2500), 0x605489805589a05689c05789e00885200985400a85601c85801d85a01e86201f)
                mstore(add(solc_usr_payload, 0x2520), 0x86402687c01f89e00d000b06000121038820630000000b2b6485206585406685)
                mstore(add(solc_usr_payload, 0x2540), 0x606785c06885e06986006786606886806986a02d87c02e87e06a852085206585)
                mstore(add(solc_usr_payload, 0x2560), 0x20854066852085606b854085406c854086406c856086206d856086406c858085)
                mstore(add(solc_usr_payload, 0x2580), 0xa06d858086206e858086406f85a085a06e85a086207085a086406785c0866068)
                mstore(add(solc_usr_payload, 0x25a0), 0x85c086806985c086a06885e086606985e086807185e087206986008660718600)
                mstore(add(solc_usr_payload, 0x25c0), 0x8700728600872073862086207486208640758640864071868087a07186a08780)
                mstore(add(solc_usr_payload, 0x25e0), 0x7286a087a07186c087607286c087807686c087a07186e087407286e087607686)
                mstore(add(solc_usr_payload, 0x2600), 0xe087807786e087a072870087407687008760778700878078870087a076872087)
                mstore(add(solc_usr_payload, 0x2620), 0x407787208760788720878079872087a00d000b070000210388207a0308000215)
                mstore(add(solc_usr_payload, 0x2640), 0x6485206585406685607b85807c85a06785c06885e06986007d86207e86406786)
                mstore(add(solc_usr_payload, 0x2660), 0x606886806986a07f86c08086e08187008287207f87408087608187808287a085)
                mstore(add(solc_usr_payload, 0x2680), 0x206a85206585406685607b85807c85a07d86207e864085c06786606886806986)
                mstore(add(solc_usr_payload, 0x26a0), 0xa07f86c08086e081870082872085e06886606986807f86a08086c08186e08287)
                mstore(add(solc_usr_payload, 0x26c0), 0x0083872086006986607f86808086a08186c08286e083870084872087407f8660)
                mstore(add(solc_usr_payload, 0x26e0), 0x8086808186a08286c08386e084870085872087608086608186808286a08386c0)
                mstore(add(solc_usr_payload, 0x2700), 0x8486e085870086872087808186608286808386a08486c08586e0868700878720)
                mstore(add(solc_usr_payload, 0x2720), 0x87a08286608386808486a08586c08686e08787008887201587c01688006b8540)
                mstore(add(solc_usr_payload, 0x2740), 0x85407b854085607c854085807d854085a07e8540862089854086408a85608560)
                mstore(add(solc_usr_payload, 0x2760), 0x7d856085807e856085a089856086208b856086408c8580858089858085a08b85)
                mstore(add(solc_usr_payload, 0x2780), 0x8086208d858086408e85a085a08d85a086208f85a08640908620862091862086)
                mstore(add(solc_usr_payload, 0x27a0), 0x4092864086400d000b0700012103882093030800011564852065854066856094)
                mstore(add(solc_usr_payload, 0x27c0), 0x85809585a06785c06885e06986009686209786406786606886806986a09886c0)
                mstore(add(solc_usr_payload, 0x27e0), 0x9986e09a87009b87209887409987609a87809b87a085206a8520658540668560)
                mstore(add(solc_usr_payload, 0x2800), 0x9485809585a096862097864085c06786606886806986a09886c09986e09a8700)
                mstore(add(solc_usr_payload, 0x2820), 0x9b872085e06886606986809886a09986c09a86e09b87009c8720860069866098)
                mstore(add(solc_usr_payload, 0x2840), 0x86809986a09a86c09b86e09c87009d872087409886609986809a86a09b86c09c)
                mstore(add(solc_usr_payload, 0x2860), 0x86e09d87009e872087609986609a86809b86a09c86c09d86e09e87009f872087)
                mstore(add(solc_usr_payload, 0x2880), 0x809a86609b86809c86a09d86c09e86e09f8700a0872087a09b86609c86809d86)
                mstore(add(solc_usr_payload, 0x28a0), 0xa09e86c09f86e0a08700a187202687c06b854085409485408560958540858096)
                mstore(add(solc_usr_payload, 0x28c0), 0x854085a09785408620a285408640a385608560968560858097856085a0a28560)
                mstore(add(solc_usr_payload, 0x28e0), 0x8620a485608640a585808580a2858085a0a485808620a685808640a785a085a0)
                mstore(add(solc_usr_payload, 0x2900), 0xa685a08620a885a08640a986208620aa86208640ab864086400d000b07000121)
                mstore(add(solc_usr_payload, 0x2920), 0x038820ac0000000e100085200285400385606785c06885e06986000086600286)
                mstore(add(solc_usr_payload, 0x2940), 0x800386a02d87c02e87e00088400288600388800885c085c06885c085e06985c0)
                mstore(add(solc_usr_payload, 0x2960), 0x86000a85e085e07185e087a0718600878072860087a071874087607287408780)
                mstore(add(solc_usr_payload, 0x2980), 0x76874087a03087608760768760878077876087a0328780878078878087a03687)
                mstore(add(solc_usr_payload, 0x29a0), 0xa087a00d000b08000021038820ad040100021500852002854003856004858005)
                mstore(add(solc_usr_payload, 0x29c0), 0x85a06785c06885e06986000686200786400086600286800386a00486c00586e0)
                mstore(add(solc_usr_payload, 0x29e0), 0x0687000787207f87408087608187808287a00088400288600388800488a00588)
                mstore(add(solc_usr_payload, 0x2a00), 0xc00688e007890085c00885c06885e06986007f87408087608187808287a01587)
                mstore(add(solc_usr_payload, 0x2a20), 0xc01688000a85e085e07f85e086008085e087408185e087608285e087808385e0)
                mstore(add(solc_usr_payload, 0x2a40), 0x87a00c8600860081860087408286008760838600878084860087a00e87408740)
                mstore(add(solc_usr_payload, 0x2a60), 0x8387408760848740878085874087a04387608760858760878086876087a04587)
                mstore(add(solc_usr_payload, 0x2a80), 0x80878087878087a04787a087a00d000b08000121038820ae0401000115008520)
                mstore(add(solc_usr_payload, 0x2aa0), 0x0285400385601885801985a06785c06885e06986001a86201b86400086600286)
                mstore(add(solc_usr_payload, 0x2ac0), 0x800386a01886c01986e01a87001b87209887409987609a87809b87a000884002)
                mstore(add(solc_usr_payload, 0x2ae0), 0x88600388801888a01988c01a88e01b890085c00885c06885e069860098874099)
                mstore(add(solc_usr_payload, 0x2b00), 0x87609a87809b87a02687c00a85e085e09885e086009985e087409a85e087609b)
                mstore(add(solc_usr_payload, 0x2b20), 0x85e087809c85e087a01d860086009a860087409b860087609c860087809d8600)
                mstore(add(solc_usr_payload, 0x2b40), 0x87a01f874087409c874087609d874087809e874087a053876087609e87608780)
                mstore(add(solc_usr_payload, 0x2b60), 0x9f876087a05587808780a0878087a05787a087a00d000b080001058520118520)
                mstore(add(solc_usr_payload, 0x2b80), 0x11852005858008060d000b0900000585401185401185400585a008060d000b09)
                mstore(add(solc_usr_payload, 0x2ba0), 0x000105856011856011856005862008060d000b0900011b00021b000305860008)
                mstore(add(solc_usr_payload, 0x2bc0), 0x108b200585201185201185800daf060585401185401185a00db0060585601185)
                mstore(add(solc_usr_payload, 0x2be0), 0x601186200db1060d000b090001191f0000000000000000000000000000000000)
                mstore(add(solc_usr_payload, 0x2c00), 0x0000000000000000000000000000000016e98a681dca730dcbe651aec5493976)
                mstore(add(solc_usr_payload, 0x2c20), 0x11944be61932e7d19a63786871335939b0eefa7e32507b68b4ad6fd89a5c1028)
                mstore(add(solc_usr_payload, 0x2c40), 0x0000000000000000000000000000000010e6ae8d3becb251e60db7d788be7029)
                mstore(add(solc_usr_payload, 0x2c60), 0x8dbcdfdbb394da2ca9725e07485d6b630569a66ec867aa0d605573ae82d550df)
                mstore(add(solc_usr_payload, 0x2c80), 0x000000000000000000000000000000000fb2ef3076aa1a8068bec7ef35167c1c)
                mstore(add(solc_usr_payload, 0x2ca0), 0xf1f26a24abaa3b4dc8c6d218021c08429e4c175654b5996eb4de74d17a5c188d)
                mstore(add(solc_usr_payload, 0x2cc0), 0x00000000000000000000000000000000000f94fa3dcc144ffe6a4ace1de5f956)
                mstore(add(solc_usr_payload, 0x2ce0), 0x76ad02ffc32c0345767b466f064aec3f1101ecd9eaf91ba5d4c145f792d1285a)
                mstore(add(solc_usr_payload, 0x2d00), 0x0000000000000000000000000000000016909a26057dec4152b5bd207c37f9a8)
                mstore(add(solc_usr_payload, 0x2d20), 0xc3af2c8cfa63dfd83e34704255392445fae3c47d749e435e0291232659a8caeb)
                mstore(add(solc_usr_payload, 0x2d40), 0x0000000000000000000000000000000000b9edb176686ec391a3684928dc0842)
                mstore(add(solc_usr_payload, 0x2d60), 0x80c60eca091b8a3925e31ef1032793f2ef4e31225ab560bf721f17525dd476c8)
                mstore(add(solc_usr_payload, 0x2d80), 0x0000000000000000000000000000000014861e20b064f637d60cc250ff3b8804)
                mstore(add(solc_usr_payload, 0x2da0), 0x9b9697b5245d031c784398bdf950e99d7968c86e92c4ec1cb3821a69686dfb09)
                mstore(add(solc_usr_payload, 0x2dc0), 0x000000000000000000000000000000000c117b524f84a06b024a40003e1c3aab)
                mstore(add(solc_usr_payload, 0x2de0), 0x25253a3cf5b53d2f77d1f9328a9c0b32bea4f591eb470dbb599b5fbdfa7df46b)
                mstore(add(solc_usr_payload, 0x2e00), 0x000000000000000000000000000000001420bb2d8c182dda6c982eb820e035f6)
                mstore(add(solc_usr_payload, 0x2e20), 0xa4a5c6c69376dfda17ac5588d34a0b313800b8d18ecd818f3e4e2671589ec691)
                mstore(add(solc_usr_payload, 0x2e40), 0x0000000000000000000000000000000000855eb6333071d5bb90a0351dbf958c)
                mstore(add(solc_usr_payload, 0x2e60), 0x13e5648bcafb55776c78e46031e4620cfda02728e26bb97f067a9a0cdf72aa9f)
                mstore(add(solc_usr_payload, 0x2e80), 0x000000000000000000000000000000000707698990b767903c9aaf028c98b46a)
                mstore(add(solc_usr_payload, 0x2ea0), 0xc4925e4e30db42105aade1a5cd7dd9b3d2222bd7085071b5c2212709cfcc2d46)
                mstore(add(solc_usr_payload, 0x2ec0), 0x000000000000000000000000000000000a88a7d4f1148bd3efffaedb5be62777)
                mstore(add(solc_usr_payload, 0x2ee0), 0x27fad92f1005d28d12ef861b5dcf8b580a1322048d469da5f84b26fa7f8d2e4d)
                mstore(add(solc_usr_payload, 0x2f00), 0x000000000000000000000000000000001495975f8f8c0cb6c54e1163fe045732)
                mstore(add(solc_usr_payload, 0x2f20), 0x2be3eb4af919cb0eb6126028ebeab81d075dff85aa522989166bf6e01880c1be)
                mstore(add(solc_usr_payload, 0x2f40), 0x0000000000000000000000000000000018bdd4eef361f4a6d23a6511b48e20fb)
                mstore(add(solc_usr_payload, 0x2f60), 0x4080898637660f3f3371adfb48585dd2ad89c29cc260d604ce9cd68a31ff427d)
                mstore(add(solc_usr_payload, 0x2f80), 0x00000000000000000000000000000000166c1cd47b07ac0aee553f0b4277cf37)
                mstore(add(solc_usr_payload, 0x2fa0), 0xb4822422a23ea90486c60a5b3b9052dff113041d51718304e781a5a7bd93bdc2)
                mstore(add(solc_usr_payload, 0x2fc0), 0x00000000000000000000000000000000016c91bfb3ce38ba23df779d69abeaa4)
                mstore(add(solc_usr_payload, 0x2fe0), 0x8aaa142a59667ce4eabfaf36c5453af4aaec6e596ad923693a2a7d1483c2fd20)
                mstore(add(solc_usr_payload, 0x3000), 0x000000000000000000000000000000001262dde7fc4aeca256572897f5d601ef)
                mstore(add(solc_usr_payload, 0x3020), 0x5b8b5586b8593d43cbcd11d2fd80fe2a2214269e5479b5d976cf507d5262c273)
                mstore(add(solc_usr_payload, 0x3040), 0x0000000000000000000000000000000012bd810c9b8eaaf899f161e2d8c26762)
                mstore(add(solc_usr_payload, 0x3060), 0xc3f299919bfa2b2809a027cc9bcac1799ef2d48b11403ce47a5341f7307d2cd4)
                mstore(add(solc_usr_payload, 0x3080), 0x00000000000000000000000000000000096d06362268ed80162468c5e664e2bb)
                mstore(add(solc_usr_payload, 0x30a0), 0x1a1a3b60a6c419cb6edb470b646e9ed4e021686e93f82d0c3ee2448368fe81be)
                mstore(add(solc_usr_payload, 0x30c0), 0x0000000000000000000000000000000015ceb98a36a3576ad6db1163a0a98d2a)
                mstore(add(solc_usr_payload, 0x30e0), 0x0535a28ca330834bb07c6682d32b20cd8171f4c0d9f063d768b6e3185b6ae44e)
                mstore(add(solc_usr_payload, 0x3100), 0x0000000000000000000000000000000019731a2f803950b978082f57fdfffb38)
                mstore(add(solc_usr_payload, 0x3120), 0x0de3c6bef55492c30e409d77ac9acb523958dea2856b12cb4e87608584ab499a)
                mstore(add(solc_usr_payload, 0x3140), 0x0000000000000000000000000000000005f057d8c91984630d36a0df6c2ebb07)
                mstore(add(solc_usr_payload, 0x3160), 0x3881713eb294d8cdf7bb0374cb722b7bb5080101a54638216ab4886f0276a475)
                mstore(add(solc_usr_payload, 0x3180), 0x0000000000000000000000000000000004d63c6ffcf22c5a45cbc67e299c2b3d)
                mstore(add(solc_usr_payload, 0x31a0), 0xcfd98199c525785d127006aca0f82774876a94e120b9bde61b9227ee96dc6841)
                mstore(add(solc_usr_payload, 0x31c0), 0x0000000000000000000000000000000002385e4a7b9ab571a73f07d9574152e5)
                mstore(add(solc_usr_payload, 0x31e0), 0xa45de038325c587523413d98b5feb6d2071c293abbeab53bf941d76b264f3369)
                mstore(add(solc_usr_payload, 0x3200), 0x000000000000000000000000000000000eea9ee53f693242e50678f2ac4a5053)
                mstore(add(solc_usr_payload, 0x3220), 0x6bc4aa60deae574c46e3cf56a8d14af17d603f8c222728fb09300eee5c5b326b)
                mstore(add(solc_usr_payload, 0x3240), 0x0000000000000000000000000000000014aa3a043bb1340472428a1756ad82bb)
                mstore(add(solc_usr_payload, 0x3260), 0x49fa2fee5ff945799006e851969947efb6351c7642b2683deb31537ea6209643)
                mstore(add(solc_usr_payload, 0x3280), 0x000000000000000000000000000000000b7028c202ee5b6a74d6ccfe5990dc98)
                mstore(add(solc_usr_payload, 0x32a0), 0x4381d45aa22ccb019d848829dd72d16143e5af158899fcc009d5ca17c97c3414)
                mstore(add(solc_usr_payload, 0x32c0), 0x0000000000000000000000000000000006c6ca7119058dbb54d5302f125f9cef)
                mstore(add(solc_usr_payload, 0x32e0), 0xdc6b68957c7b970427a4b5a3bd0aa7ff5fa033687afdc2a4e150a408b0a5f4d2)
                mstore(add(solc_usr_payload, 0x3300), 0x0000000000000000000000000000000008a540ee790774da565637ec30ced988)
                mstore(add(solc_usr_payload, 0x3320), 0x563c90d314d01996465fa3f893d5fb010b617a4edcabc5c8f8141584792a0067)
                mstore(add(solc_usr_payload, 0x3340), 0x00000000000000000000000000000000071e81991f7c8f62be7df37cd485cb5e)
                mstore(add(solc_usr_payload, 0x3360), 0x1f941d942cc15f814350867bcdf1521ef6e7e76b6928827688b0d3d14a6cf1a3)
                mstore(add(solc_usr_payload, 0x3380), 0x0000000000000000000000000000000005a4ed142d6c05e535a91ff8244ca5cb)
                mstore(add(solc_usr_payload, 0x33a0), 0xdda66355e156c19ea759a1f5aecd1225e16cb3f18397a66b055a2918a2a74d54)
                mstore(add(solc_usr_payload, 0x33c0), 0x000000000000000000000000000000000ce5eb9724134cce6feb1c0ff1b66ab3)
                mstore(add(solc_usr_payload, 0x33e0), 0x5e79b2b4087200f1d9a76ee4a2b3b5424266da9d518653e9391e9a94196f1d7f)
                mstore(add(solc_usr_payload, 0x3400), 0x0000000000000000000000000000000009b07c1df13d348c1ed7cb560fcdd682)
                mstore(add(solc_usr_payload, 0x3420), 0x55221aadb75410fa4526857c95cea6bf3a0efa98e31898de56ea7ff30f7c514a)
                mstore(add(solc_usr_payload, 0x3440), 0x0000000000000000000000000000000011b2d20f8b12527aba78064c809753e2)
                mstore(add(solc_usr_payload, 0x3460), 0x21cebde9bb41aa67abae156e3a179655388e51211ba5614fb696a7f0cc212560)
                mstore(add(solc_usr_payload, 0x3480), 0x0000000000000000000000000000000010ce280498c90ca7501427caf6bcd6d9)
                mstore(add(solc_usr_payload, 0x34a0), 0xb4987380f8d9e8ef710b81034a460c8da32362568e1e9fd6b2cb5297805c98ad)
                mstore(add(solc_usr_payload, 0x34c0), 0x000000000000000000000000000000000292967ae2e91be4d3555cddb84538dd)
                mstore(add(solc_usr_payload, 0x34e0), 0x0edcb077ce0626f751bee2673ff6b24c182fd2ae99a0cd83881a81a3facfcb6e)
                mstore(add(solc_usr_payload, 0x3500), 0x0000000000000000000000000000000017cf661d855e771f61cab52918bc03e5)
                mstore(add(solc_usr_payload, 0x3520), 0x329761bebc6704041c0430c64bc2d589210a4250f57e9dec51a807d4d6926f31)
                mstore(add(solc_usr_payload, 0x3540), 0x000000000000000000000000000000000f50cacb58bf9101f3d7926b2e26675d)
                mstore(add(solc_usr_payload, 0x3560), 0x036c7cf34f335946dfc1d1a6e148de3da13cabfe8e7507f10baca11e07231413)
                mstore(add(solc_usr_payload, 0x3580), 0x0000000000000000000000000000000016caf868eda0aeb753fd8ec3bee96cbe)
                mstore(add(solc_usr_payload, 0x35a0), 0x3217eade0bae8e908b6cfe1f144518cbaec5bbbbc6e6641d82702b3dd5997985)
                mstore(add(solc_usr_payload, 0x35c0), 0x000000000000000000000000000000000a35da0b540c40574d639e726b9c7e6d)
                mstore(add(solc_usr_payload, 0x35e0), 0xb45e6cbefb614f14a1721bdbca2dfcb20aaeb64926032522ba3de23420dc1d87)
                mstore(add(solc_usr_payload, 0x3600), 0x000000000000000000000000000000000b7f1691be78a38c579c2ac6bef18d54)
                mstore(add(solc_usr_payload, 0x3620), 0xf2d63e634590931fda91cce7af80f7c589cc37a98870e127c93e059ff020df07)
                mstore(add(solc_usr_payload, 0x3640), 0x0000000000000000000000000000000012582699af0164d4335252425d0251c4)
                mstore(add(solc_usr_payload, 0x3660), 0xa1af4e259a3f65f0065b2b05127538a8434de1326c4920ee45da346bbbc7d293)
                mstore(add(solc_usr_payload, 0x3680), 0x000000000000000000000000000000000e004abc0ac243147c480dca32186a34)
                mstore(add(solc_usr_payload, 0x36a0), 0x78642aaafe922adde54e02ae93479fa0ae45b75ed0229c2f358a0473d17c09a5)
                mstore(add(solc_usr_payload, 0x36c0), 0x0000000000000000000000000000000013e0dac8358fff676678a7b7d854aee3)
                mstore(add(solc_usr_payload, 0x36e0), 0x3fda118cfb39d426f3418966ed06283adbd804fbe8cf51fd89c2f5c410919f48)
                mstore(add(solc_usr_payload, 0x3700), 0x00000000000000000000000000000000168c0d6883d0d5b67d3a5944ee0616a3)
                mstore(add(solc_usr_payload, 0x3720), 0xce7ac537685a26b678bab6b1b50115c32a5f90b6ca56cb8560a40964840893ce)
                mstore(add(solc_usr_payload, 0x3740), 0x00000000000000000000000000000000197d467f656fc49a1c5119d7cd826cc2)
                mstore(add(solc_usr_payload, 0x3760), 0xbe6345c67f108e7e44f8ebfcebea5366fdee85d69947c8f74f623165dc1029b5)
                mstore(add(solc_usr_payload, 0x3780), 0x00000000000000000000000000000000133f78d1d5ad537d358f421d115bdb2f)
                mstore(add(solc_usr_payload, 0x37a0), 0x44eff93e623017fb4a06006877bd8504b8b614c6c877d73de7cdc2c2e69a8998)
                mstore(add(solc_usr_payload, 0x37c0), 0x00000000000000000000000000000000067b406b38e3895daddca2f64de3ee21)
                mstore(add(solc_usr_payload, 0x37e0), 0x5c7961f1d2f1904f7e2aa60bc20559610c868810183505527e28eea6089d6bf8)
                mstore(add(solc_usr_payload, 0x3800), 0x000000000000000000000000000000000bd679e559d6bf9f498928a3074a0709)
                mstore(add(solc_usr_payload, 0x3820), 0x23c4cf1d5823b59316852fd6653fe003a4a2da9ba443e4640993524c79a6f56d)
                mstore(add(solc_usr_payload, 0x3840), 0x000000000000000000000000000000000821077b092335b9f70fb79a424cca13)
                mstore(add(solc_usr_payload, 0x3860), 0x4e823d96a4fdeaf4154ab7c5ef023844695a10e9bfdf314847ccaa40205f980a)
                mstore(add(solc_usr_payload, 0x3880), 0x00000000000000000000000000000000041f7c88095a1bbf5759d88a7d109853)
                mstore(add(solc_usr_payload, 0x38a0), 0x4b1661f3b1b9012866e17c7550a5b52861ac915beba38767c7aeb04c1df330ac)
                mstore(add(solc_usr_payload, 0x38c0), 0x000000000000000000000000000000000f2e8cc95c27bf0235efa88fa70bb3eb)
                mstore(add(solc_usr_payload, 0x38e0), 0x59a5ef2602a9b70c5af7b0db755f10a8e0ffc380b61a580c3300fda8d6077854)
                mstore(add(solc_usr_payload, 0x3900), 0x000000000000000000000000000000001983933b9a69c960c9eda1f5942af11a)
                mstore(add(solc_usr_payload, 0x3920), 0x22de694e7c8b2a5f8d920b50d6c90aca30d149ace5ff9feebf84a136abdfa9f4)
                mstore(add(solc_usr_payload, 0x3940), 0x00000000000000000000000000000000162f68d07437f5dd432392f6a244044d)
                mstore(add(solc_usr_payload, 0x3960), 0x4605b4457384fb65577df046c667a744f851fbdb0e8751aaeeb334bf32fbd3e0)
                mstore(add(solc_usr_payload, 0x3980), 0x0000000000000000000000000000000014669fe860d72f984d085b33bfffa399)
                mstore(add(solc_usr_payload, 0x39a0), 0x12a9b0d0acb1ff8fd119eee9d0870eab9324293b88df67b9e1ebd180db262c72)
                mstore(add(solc_usr_payload, 0x39c0), 0x000000000000000000000000000000000f3292f0f7b5707fe0874c56fdae2e88)
                mstore(add(solc_usr_payload, 0x39e0), 0x2a2ba44cc1a14f736d255905838f8438fb8dbfd65ad84bcbca748a749c58955e)
                mstore(add(solc_usr_payload, 0x3a00), 0x000000000000000000000000000000000ee7e9d684b203f28dd5424f3a511695)
                mstore(add(solc_usr_payload, 0x3a20), 0xff88a9d696976adca8c54262e0f553756ec45b8e103453f8c18a07c3abcef5fd)
                mstore(add(solc_usr_payload, 0x3a40), 0x00000000000000000000000000000000177029152e262c258c987bfbeeee14c8)
                mstore(add(solc_usr_payload, 0x3a60), 0xe945c114efada4abdeff8610bea0cf199ef3f375cf15f6b437de67f3379c5801)
                mstore(add(solc_usr_payload, 0x3a80), 0x000000000000000000000000000000000e2ead1ec1acc411940e7bea5d0f2114)
                mstore(add(solc_usr_payload, 0x3aa0), 0x6b39327e36ebab84013dd8f5c2b3f8b576a125db88ff28db45a79a28df414b66)
                mstore(add(solc_usr_payload, 0x3ac0), 0x00000000000000000000000000000000199b4ea033c01e1d83627c054ba6f2dc)
                mstore(add(solc_usr_payload, 0x3ae0), 0x2a61b1277d07469ad65c413a1970c9cf179bedfc4cf2f61c1ee8ca5e4a01ab90)
                mstore(add(solc_usr_payload, 0x3b00), 0x0000000000000000000000000000000011af8f4e99c419588e05414f664ae8f6)
                mstore(add(solc_usr_payload, 0x3b20), 0xdded731799d69d8f5a72c124a5c6df33153e15767000ef54648a8dd23687140a)
                mstore(add(solc_usr_payload, 0x3b40), 0x0000000000000000000000000000000017ba99d9323e45fe54ec6ac4daaad8d3)
                mstore(add(solc_usr_payload, 0x3b60), 0x0c0dbc53d3f5f54c05667eb0e4f28da8973657bf62915fcdfc551698f56aa574)
                mstore(add(solc_usr_payload, 0x3b80), 0x000000000000000000000000000000000ed68fa806cd3171cb061afebf65799d)
                mstore(add(solc_usr_payload, 0x3ba0), 0xf9014492a08de2420f1234158d2f1d214b5354b7ad8cfc753d2712e6bb9b20a5)
                mstore(add(solc_usr_payload, 0x3bc0), 0x0000000000000000000000000000000013f05c6e0393baeec023451082007353)
                mstore(add(solc_usr_payload, 0x3be0), 0x55211ac5dd3c2267dcf706d18263fa7b7916e44ab1d5309430542f75717187c4)
                mstore(add(solc_usr_payload, 0x3c00), 0x000000000000000000000000000000000a925e4ad4c2d71f096de0e53baea720)
                mstore(add(solc_usr_payload, 0x3c20), 0x7a90226e678437d20f2ec9ae630075a12ae88a186bcfba1bc0444e5bc40245e7)
                mstore(add(solc_usr_payload, 0x3c40), 0x0000000000000000000000000000000006ff1ce2b5e6c2c3cedd7a8465c5ed3a)
                mstore(add(solc_usr_payload, 0x3c60), 0x72e4496eead09ba2cd0ef56fdd94942ed738b42b71caea3d1bd78b0ae3ec3f96)
                mstore(add(solc_usr_payload, 0x3c80), 0x000000000000000000000000000000000190af4fe845524352a9f624463ae7ca)
                mstore(add(solc_usr_payload, 0x3ca0), 0x406fa14f4319031fe5a7630ab2bd66c107d6cb05fa65b98ee0c5f0234c29d189)
                mstore(add(solc_usr_payload, 0x3cc0), 0x0000000000000000000000000000000013036a5f7dca90b530955bf735da2920)
                mstore(add(solc_usr_payload, 0x3ce0), 0x29b8759dc69e53d6c830a3bee081165d4d59442dacb50c2a06aded3193e88387)
                mstore(add(solc_usr_payload, 0x3d00), 0x0000000000000000000000000000000012b6e22b800c1a2dfde554f3312f4b50)
                mstore(add(solc_usr_payload, 0x3d20), 0x1b75400de7c8c476dcc9fd72dcef80d9384da4e4af8f928a07e4a9fa485da8bc)
                mstore(add(solc_usr_payload, 0x3d40), 0x00000000000000000000000000000000053da19ebda674bbc95d3d10ad04cb96)
                mstore(add(solc_usr_payload, 0x3d60), 0xa410aecead2c7059df1e12a1a56117a830f0008a91551cec88f1ad548a379dfe)
                mstore(add(solc_usr_payload, 0x3d80), 0x0000000000000000000000000000000016038223f354e7d7c75614116c58b1c9)
                mstore(add(solc_usr_payload, 0x3da0), 0x866a8a39d6b30ea560b263c68da7e78210b2f2a7f9b19564388f2f2370d7cd6a)
                mstore(add(solc_usr_payload, 0x3dc0), 0x000000000000000000000000000000000bdb1d40f473070bfa087ff87bc9c86d)
                mstore(add(solc_usr_payload, 0x3de0), 0x0d57398e71f45845ebcd0aa24a9ea829718dfce700af80fab46b51ad73fb58f6)
                mstore(add(solc_usr_payload, 0x3e00), 0x00000000000000000000000000000000085c579504429306bbf0ec28b07f91a6)
                mstore(add(solc_usr_payload, 0x3e20), 0x7326fabf9ec866a45ef4d294f390a7c497c7b990a62b602f5999fcaee0e7e9bc)
                mstore(add(solc_usr_payload, 0x3e40), 0x000000000000000000000000000000000b042dab28398e8c0670ee6f04cca93a)
                mstore(add(solc_usr_payload, 0x3e60), 0xa41ecc7205c8216513d027b4c1213d0e452c16898d7b2c811027598cf2715dc3)
                mstore(add(solc_usr_payload, 0x3e80), 0x00000000000000000000000000000000093b6ec41dd5c2455b9d2dca635c472d)
                mstore(add(solc_usr_payload, 0x3ea0), 0x386496c219c45db9f1a5d96c179d1028694626c4a1845aef384efaaa8053284b)
                mstore(add(solc_usr_payload, 0x3ec0), 0x000000000000000000000000000000000386d1128886a4a879e8a93aa84b6525)
                mstore(add(solc_usr_payload, 0x3ee0), 0x1061026f4dae08952816961f9d6fc0b8153784a5961f831b68f1e2ddc567efb7)
                mstore(add(solc_usr_payload, 0x3f00), 0x0000000000000000000000000000000000b6ed6814a099c4e435e42fc8ee4250)
                mstore(add(solc_usr_payload, 0x3f20), 0x0e16b88c78069cebe20e4d647c8bb44acd6b9c6712d53a3ebd014e54a1a75e89)
                mstore(add(solc_usr_payload, 0x3f40), 0x0000000000000000000000000000000001ae3805b59b2f2d53a59e2c19001e97)
                mstore(add(solc_usr_payload, 0x3f60), 0xaace57ac2ba8b58550a740e897ba6278e409291e5c87466a01edd7cbe3b99f88)
                mstore(add(solc_usr_payload, 0x3f80), 0x000000000000000000000000000000000ca3af5a65ec51141f694db29736dd57)
                mstore(add(solc_usr_payload, 0x3fa0), 0xa1cdbfa79f45aa80a6cdda8de3d51c4b16c95361b412c6f47e132eae7b69f7f7)
                mstore(add(solc_usr_payload, 0x3fc0), 0x0000000000000000000000000000000018dc16284e57fccd755058b259b913c7)
                mstore(add(solc_usr_payload, 0x3fe0), 0x7a54da0d0e206b7906878fd3e994ad04c66f48e19cd982d5651f99b48b992064)
                mstore(add(solc_usr_payload, 0x4000), 0x00000000000000000000000000000000197560c82bf47486bee750469d626ce4)
                mstore(add(solc_usr_payload, 0x4020), 0x2d40ce7489ff61a64a0eb55e6672926a40f06348ab575f926fbe4d87b672fcd7)
                mstore(add(solc_usr_payload, 0x4040), 0x0000000000000000000000000000000007b4f39a579a01d4f01f4ab9bc841a7d)
                mstore(add(solc_usr_payload, 0x4060), 0xe70541d6b79945e9569fd59388739f5b4ce57794044d287d7b0b58e35198caab)
                mstore(add(solc_usr_payload, 0x4080), 0x0000000000000000000000000000000004e1b539a3a123291eaa8c85be3395e7)
                mstore(add(solc_usr_payload, 0x40a0), 0x9c6845178d995313daf42680692210e1ec79278ec8b6e2da1d6f289609100404)
                mstore(add(solc_usr_payload, 0x40c0), 0x0000000000000000000000000000000010d56b62afe35890b4f98b946daa8936)
                mstore(add(solc_usr_payload, 0x40e0), 0xd83e014595585e2892e21bfc5e86f84d404b435dc1a689539d74773aba55dad4)
                mstore(add(solc_usr_payload, 0x4100), 0x000000000000000000000000000000000f227bcaef796cabf0a93289fb8321e9)
                mstore(add(solc_usr_payload, 0x4120), 0x1d43880fa5fcebab73c77c6bb406cc5e9386a81774635b5a6144b75ef10cd994)
                mstore(add(solc_usr_payload, 0x4140), 0x000000000000000000000000000000000a849d95d37e501cc6272f325f88d677)
                mstore(add(solc_usr_payload, 0x4160), 0xb25be83ce57eb9c32d382613930bbc0ef7ec349d44ac74a9383c111efcb73783)
                mstore(add(solc_usr_payload, 0x4180), 0x000000000000000000000000000000000b77ada25b279742ec75d2014583ad79)
                mstore(add(solc_usr_payload, 0x41a0), 0x427bfa99ab8a941648e1a11084fec2a6fdb8192f498cf3e272a5e786597273a1)
                mstore(add(solc_usr_payload, 0x41c0), 0x00000000000000000000000000000000056788c108fd40583888b8771a70d3f6)
                mstore(add(solc_usr_payload, 0x41e0), 0x364290f978d1fc201c0a76561a4c1cdde7643f7d76448dad2586c3eac2e34104)
                mstore(add(solc_usr_payload, 0x4200), 0x0000000000000000000000000000000002ecf71916494d46153fdd513ead1917)
                mstore(add(solc_usr_payload, 0x4220), 0x06401b48839713727c920f4591fe09ac3e8f4140ef1cd9e39b0d0bbe0b5b87d4)
                mstore(add(solc_usr_payload, 0x4240), 0x000000000000000000000000000000000e7bab8cc3c714f06826c8f3695dc63c)
                mstore(add(solc_usr_payload, 0x4260), 0xe7e931ff0dbe009cbb84fef0b99124905d90cdd6f5356a7ee7673548f6f0692c)
                return(solc_usr_runtime, 0x4281)
            }

        }
        

    }
    
    object "Halo2VerifyingKey_302_deployed" {
        code {
            
            mstore(64, memoryguard(128))

            revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()

            function shift_right_224_unsigned(value) -> newValue {
                newValue :=

                shr(224, value)

            }

            function allocate_unbounded() -> memPtr {
                memPtr := mload(64)
            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

        }

        data ".metadata" hex"a164736f6c634300081e000a"
    }

}

/-- The runtime sub-object name solc gives `Halo2VerifyingKey`. Surface.irRuntime
    (Lowering/Surface.lean:467) resolves it through S.runtimeName ir.name, so this
    is the string a Surface must return for the imported object to be the one a run
    talks about. -/
def vkRuntimeName : String := "Halo2VerifyingKey_302_deployed"

/-- The deployed runtime sub-object of vkIr, as an object: it carries the .metadata
    data segment the creation object refers to by name. The none arm is unreachable and
    irShape_ok is what says so. -/
def vkRuntimeObject : Object EVM.Op :=
  match vkIr.subObject vkRuntimeName with
  | some o => o
  | none => vkIr

/-- The deployed runtime block: the block RunContractIR runs. -/
def vkRuntime : Block EVM.Op := Object.codeBlock vkRuntimeObject

/-- The creation object code block: where setimmutable lives. The deployed side
    only ever reads immutables, through loadimmutable. -/
def vkCreation : Block EVM.Op := Object.codeBlock vkIr

/-! ### Reading the artifact back -/

/-- The committed artifact paths, relative to formal/, which is where lake build and
    scripts/checks.sh run. A missing file is a RED gate, never a silent true, and the
    reachability gate comes first so a moved path is diagnosed rather than matched by nothing
    (the standing D-P19 note). -/
def verifierArtifactPath : String := "Midfall/Yul/solc-ir-Halo2Verifier.yul"
def vkArtifactPath : String := "Midfall/Yul/solc-ir-Halo2VerifyingKey.yul"

def callsitesPath : String := "Midfall/Yul/solc-ir-callsites.tsv"

def readIrArtifact (path : String) : IO String :=
  [path, "formal/" ++ path].foldl
    (fun (acc : IO String) (p : String) =>
      acc >>= fun got =>
        if got != "" then pure got
        else (try IO.FS.readFile p catch _ => pure ""))
    (pure "")

/-- FNV-1a over the artifact bytes. Not a cryptographic digest - the point is drift, not
    security - chosen because the file is 190 KB and folding that through the pure-Lean keccak
    of Midfall.Common at elaboration time would be slow. The sha256 of the same bytes is in
    each import doc string above for anyone who wants to check it with shasum. -/
def irDigest (s : String) : UInt64 :=
  s.toUTF8.data.foldl (fun (h : UInt64) (c : UInt8) =>
    (h ^^^ c.toUInt64) * 1099511628211) 14695981039346656037

/-- The identifier scan, re-implemented in Lean from the same specification the generator uses:
    drop slash-slash comments, blank out string literals, collect the identifier lexeme. Two
    independent lexers over one committed artifact is the point - irRename_ok compares what
    each of them sees. -/
structure IrScan where
  ids : List String
  cur : String
  inStr : Bool
  esc : Bool
  slash : Bool
  comment : Bool

def irScanInit : IrScan :=
  { ids := [], cur := "", inStr := false, esc := false, slash := false, comment := false }

def irIdentChar (c : Char) : Bool := (c.isAlpha || c.isDigit) || c == '_' || c == '$'

def irFlush (st : IrScan) : IrScan :=
  if st.cur.isEmpty then st
  else { st with cur := "", ids := st.cur :: st.ids }

def irStepDefault (st : IrScan) (c : Char) : IrScan :=
  if irIdentChar c && (!st.cur.isEmpty || c.isAlpha || c == '_' || c == '$') then
    { st with cur := st.cur.push c }
  else
    let st := irFlush st
    if c == '"' then { st with inStr := true }
      else if c == '/' then { st with slash := true }
      else st

def irStep (st : IrScan) (c : Char) : IrScan :=
  if st.comment then
    if c == '\n' then { st with comment := false } else st
  else if st.inStr then
    if st.esc then { st with esc := false }
    else if c == '\\' then { st with esc := true }
    else if c == '"' then { st with inStr := false }
    else st
  else if st.slash then
    let st := irFlush { st with slash := false }
    if c == '/' then { st with comment := true } else irStepDefault st c
  else irStepDefault st c

def irIdents (s : String) : List String :=
  (irFlush (s.toList.foldl irStep irScanInit)).ids.reverse

/-- The reserved list of DECISION 2, as data, so the gates are about the real rule. -/
def irReserved : List String := ["end"]

/-- Does this name need the alpha-rename? -/
def irNeedsRen (x : String) : Bool := x.contains '$' || irReserved.contains x

/-- The rename rule, character for character the generator's ren. -/
def irRen (x : String) : String :=
  if irNeedsRen x then "solc_" ++ x.replace "$" "_" else x

/-- The renamed names of one artifact, as the Lean lexer sees them. -/
def irRenamedOf (path : String) : IO (List String) := do
  pure ((irIdents (← readIrArtifact path)).eraseDups.filter irNeedsRen)

def verifierRenamed : IO (List String) := irRenamedOf verifierArtifactPath
def vkRenamed : IO (List String) := irRenamedOf vkArtifactPath

-- Every identifier the AST carries: variable references, user-call targets, function names,
-- parameters and return names.
mutual
partial def exprNames : Expr EVM.Op -> List String
  | .lit _ => []
  | .var x => [x]
  | .builtin _ args => args.flatMap exprNames
  | .call fn args => fn :: args.flatMap exprNames

partial def stmtNames : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtNames
  | .funDef n ps rs b => n :: ps ++ rs ++ b.flatMap stmtNames
  | .letDecl vs e => vs ++ (e.map exprNames).getD []
  | .assign vs e => vs ++ exprNames e
  | .cond c b => exprNames c ++ b.flatMap stmtNames
  | .switch c cs d => exprNames c ++ cs.flatMap (fun (_, b) => b.flatMap stmtNames)
      ++ (d.map (fun b => b.flatMap stmtNames)).getD []
  | .forLoop i c p b => i.flatMap stmtNames ++ exprNames c ++ p.flatMap stmtNames
      ++ b.flatMap stmtNames
  | .exprStmt e => exprNames e
  | .break | .continue | .leave => []
end

partial def objectNames (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtNames ++ (o.subObjects.map objectNames).flatten

-- The builtin call sites, as opNames: the quantity the manifest
-- Midfall/Yul/ir-builtins.tsv counts in the artifact text. Two independent routes to the
-- same number, compared by gate 6.
mutual
partial def exprBuiltinCalls : Expr EVM.Op -> List String
  | .lit _ => []
  | .var _ => []
  | .builtin op args => opName op :: args.flatMap exprBuiltinCalls
  | .call _ args => args.flatMap exprBuiltinCalls

partial def stmtBuiltinCalls : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtBuiltinCalls
  | .funDef _ _ _ b => b.flatMap stmtBuiltinCalls
  | .letDecl _ e => (e.map exprBuiltinCalls).getD []
  | .assign _ e => exprBuiltinCalls e
  | .cond c b => exprBuiltinCalls c ++ b.flatMap stmtBuiltinCalls
  | .switch c cs d => exprBuiltinCalls c
      ++ cs.flatMap (fun (_, b) => b.flatMap stmtBuiltinCalls)
      ++ (d.map (fun b => b.flatMap stmtBuiltinCalls)).getD []
  | .forLoop i c p b => i.flatMap stmtBuiltinCalls ++ exprBuiltinCalls c
      ++ p.flatMap stmtBuiltinCalls ++ b.flatMap stmtBuiltinCalls
  | .exprStmt e => exprBuiltinCalls e
  | .break | .continue | .leave => []
end

partial def objectBuiltinCalls (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtBuiltinCalls ++ (o.subObjects.map objectBuiltinCalls).flatten

-- User-function call sites plus the definitions themselves: the manifest regex sees
-- "function f(" as one call site of f, so the AST count has to as well or gate 6 is unfair.
mutual
partial def exprUserCalls : Expr EVM.Op -> List String
  | .lit _ => []
  | .var _ => []
  | .builtin _ args => args.flatMap exprUserCalls
  | .call fn args => fn :: args.flatMap exprUserCalls

partial def stmtUserCalls : Stmt EVM.Op -> List String
  | .block b => b.flatMap stmtUserCalls
  | .funDef n ps rs b => n :: ps ++ rs ++ b.flatMap stmtUserCalls
  | .letDecl _ e => (e.map exprUserCalls).getD []
  | .assign _ e => exprUserCalls e
  | .cond c b => exprUserCalls c ++ b.flatMap stmtUserCalls
  | .switch c cs d => exprUserCalls c ++ cs.flatMap (fun (_, b) => b.flatMap stmtUserCalls)
      ++ (d.map (fun b => b.flatMap stmtUserCalls)).getD []
  | .forLoop i c p b => i.flatMap stmtUserCalls ++ exprUserCalls c
      ++ p.flatMap stmtUserCalls ++ b.flatMap stmtUserCalls
  | .exprStmt e => exprUserCalls e
  | .break | .continue | .leave => []
end

partial def objectUserCalls (o : Object EVM.Op) : List String :=
  o.codeBlock.flatMap stmtUserCalls ++ (o.subObjects.map objectUserCalls).flatten

-- Total Expr/Stmt node count: the hand-edit detector of gate 7.
mutual
partial def exprCount : Expr EVM.Op -> Nat
  | .lit _ => 0
  | .var _ => 0
  | .builtin _ args => 1 + args.foldl (fun n a => n + exprCount a) 0
  | .call _ args => 1 + args.foldl (fun n a => n + exprCount a) 0

partial def stmtCount : Stmt EVM.Op -> Nat
  | .block b => 1 + b.foldl (fun n s => n + stmtCount s) 0
  | .funDef _ _ _ b => 1 + b.foldl (fun n s => n + stmtCount s) 0
  | .letDecl _ e => 1 + (e.map exprCount).getD 0
  | .assign _ e => 1 + exprCount e
  | .cond c b => 1 + exprCount c + b.foldl (fun n s => n + stmtCount s) 0
  | .switch c cs d => 1 + exprCount c
      + cs.foldl (fun n (_, b) => n + b.foldl (fun m s => m + stmtCount s) 0) 0
      + (match d with | none => 0 | some b => b.foldl (fun n s => n + stmtCount s) 0)
  | .forLoop i c p b => 1 + i.foldl (fun n s => n + stmtCount s) 0 + exprCount c
      + p.foldl (fun n s => n + stmtCount s) 0 + b.foldl (fun n s => n + stmtCount s) 0
  | .exprStmt e => 1 + exprCount e
  | .break | .continue | .leave => 1
end

partial def objectStmtCount (o : Object EVM.Op) : Nat :=
  o.codeBlock.foldl (fun n s => n + stmtCount s) 0
    + o.subObjects.foldl (fun n s => n + objectStmtCount s) 0

/-- Literal statistics of the imported AST: the hole the call-site gate leaves open. A call-site
    count cannot see a changed LITERAL - add(x, 1) and add(x, 2) have identical call sites - so
    the number of numeric literals, their sum, the number of string literals and their total
    byte length are pinned as well (gate 10). -/
structure LitAgg where
  numCount : Nat
  numSum : Nat
  strCount : Nat
  strBytes : Nat
  strSum : Nat
  boolCount : Nat

deriving Inhabited

def litZero : LitAgg :=
  { numCount := 0, numSum := 0, strCount := 0, strBytes := 0, strSum := 0, boolCount := 0 }

def litPlus (a b : LitAgg) : LitAgg :=
  { numCount := a.numCount + b.numCount, numSum := a.numSum + b.numSum,
    strCount := a.strCount + b.strCount, strBytes := a.strBytes + b.strBytes,
    strSum := a.strSum + b.strSum, boolCount := a.boolCount + b.boolCount }

/-- The byte sum of a string literal: strBytes alone cannot see "5" rewritten to "6", so the
    characters are summed as well. -/
def strAgg (s : String) : Nat × Nat :=
  (s.length, s.toList.foldl (fun acc c => acc + c.toNat) 0)

def litOne (l : Literal) : LitAgg :=
  match l with
  | .number n => { numCount := 1, numSum := n, strCount := 0, strBytes := 0, strSum := 0,
                   boolCount := 0 }
  | .string s => { numCount := 0, numSum := 0, strCount := 1, strBytes := (strAgg s).1,
                   strSum := (strAgg s).2, boolCount := 0 }
  | .bool _ => { numCount := 0, numSum := 0, strCount := 0, strBytes := 0, strSum := 0,
                 boolCount := 1 }

mutual
partial def exprLits : Expr EVM.Op -> LitAgg
  | .lit l => litOne l
  | .var _ => litZero
  | .builtin _ args => args.foldl (fun acc e => litPlus acc (exprLits e)) litZero
  | .call _ args => args.foldl (fun acc e => litPlus acc (exprLits e)) litZero

partial def stmtLits : Stmt EVM.Op -> LitAgg
  | .block b => b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero
  | .funDef _ _ _ b => b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero
  | .letDecl _ e => e.map exprLits |>.getD litZero
  | .assign _ e => exprLits e
  | .cond c b => litPlus (exprLits c) (b.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
  | .switch c cs d =>
      cs.foldl (fun acc (_, b) => litPlus acc (b.foldl (fun m s => litPlus m (stmtLits s))
        litZero)) (litPlus (exprLits c) (match d with
        | none => litZero
        | some b => b.foldl (fun m s => litPlus m (stmtLits s)) litZero))
  | .forLoop i c p b =>
      (litPlus (i.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
        (litPlus (exprLits c)
          ((p ++ b).foldl (fun acc s => litPlus acc (stmtLits s)) litZero)))
  | .exprStmt e => exprLits e
  | .break | .continue | .leave => litZero
end

partial def objectLits (o : Object EVM.Op) : LitAgg :=
  litPlus (o.codeBlock.foldl (fun acc s => litPlus acc (stmtLits s)) litZero)
    (o.subObjects.foldl (fun acc s => litPlus acc (objectLits s)) litZero)

/-- The digest of every identifier the imported object carries, in order, separated so that a
    split cannot be faked: this is what sees an identifier edited inside the quotation. The
    call-site gate sees names that are called, the literal gate sees values, and neither sees a
    local variable renamed. -/
def objectNameDigest (o : Object EVM.Op) : UInt64 :=
  irDigest (String.join ((o.name :: objectNames o).flatMap (fun n => [n, "\n"])))

/-- The numbers PINS records, for re-measuring after a deliberate regeneration: evaluate this
    at #eval and paste the six numbers into PINS in scripts/gen_import_solc_ir.py. -/
def shapeReport : IO (List Nat) := do
  let a := objectLits verifierIr
  let b := objectLits vkIr
  pure [objectStmtCount verifierIr, objectStmtCount vkIr,
    verifierRuntime.length, vkRuntime.length,
    (objectNames verifierIr).length, (objectNames vkIr).length,
    a.numCount, a.numSum, a.strCount, a.strBytes, a.strSum, a.boolCount,
    b.numCount, b.numSum, b.strCount, b.strBytes, b.strSum, b.boolCount,
    (objectNameDigest verifierIr).toNat, (objectNameDigest vkIr).toNat]

/-! ### The prologue pin: DECISION 1, stated as a proposition -/

/-- THE PIN. The first statement of the imported deployed runtime block is exactly
    mstore(64, memoryguard(128)) - the ir value, not the irOptimized 0x08e0. This is rfl, so
    it is a build failure rather than a red gate if the artifact, the settings or the pinned
    output selection ever change. -/
theorem verifierRuntime_head_is_memoryguard :
    verifierRuntime.head? =
      some (Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])) := rfl

/-- The creation object's first statement, for the same reason: ir reserves 160 there and 128
    in the runtime, which is a fact about the artifact rather than an assumption. -/
theorem verifierCreation_head_is_memoryguard :
    verifierCreation.head? =
      some (Stmt.exprStmt (Expr.builtin Op.mstore
        [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 160)]])) := rfl

/-- The set/immutable pair, taken from the imported artifact rather than typed by hand: the
    creation object writes the immutable that the runtime object reads. This is the statement
    PLAN section 7's irCheck wants about immutables, at the level of the imported object - the
    run that exhibits it is in Midfall/Instances/ImportedIR.lean. -/
def importedSetImmutableSite : Option (Stmt EVM.Op) :=
  verifierCreation.find? fun
    | Stmt.exprStmt (Expr.builtin Op.setimmutable _) => true
    | _ => false

def importedLoadImmutableSites : Nat :=
  (objectBuiltinCalls verifierIr).filter (fun n => n == "loadimmutable") |>.length

/-! ### Gates -/

/-- GATE 1 (reachability first): both committed artifacts exist, are non-empty, and carry the
    object names the import claims. Red if a file is moved or truncated - the failure mode that
    would otherwise leave every digest gate below comparing nothing. -/
def irArtifactsReachable_ok : IO Bool := do
  let t0 <- readIrArtifact verifierArtifactPath
  let t1 <- readIrArtifact vkArtifactPath
  pure ((t0.utf8ByteSize > 1000 && t0.contains "object \"Halo2Verifier_292\" {" && t0.contains "object \"Halo2Verifier_292_deployed\" {") &&
    (t1.utf8ByteSize > 1000 && t1.contains "object \"Halo2VerifyingKey_302\" {" && t1.contains "object \"Halo2VerifyingKey_302_deployed\" {"))

#eval irArtifactsReachable_ok               -- expect true

/-- GATE 2: THE DIGEST. Re-derive a digest of each artifact at #eval time and compare with the
    value the generator measured from the bytes solc emitted (D-P19). This is the gate that
    makes the committed artifact the artifact of record: change one byte of the .yul and this
    goes red. The byte counts are pinned alongside, because a digest alone would not tell a
    reader who does not trust the hash that the file was truncated rather than edited. -/
def irArtifactDigest_ok : IO Bool := do
  let t0 <- readIrArtifact verifierArtifactPath
  let t1 <- readIrArtifact vkArtifactPath
  pure (irDigest t0 == (9842857077079826151 : UInt64) && t0.utf8ByteSize == 192150 &&
    irDigest t1 == (7388129883150509039 : UInt64) && t1.utf8ByteSize == 64329)

#eval irArtifactDigest_ok                   -- expect true

/-- GATE 3: the artifact's own shape, measured from the text rather than pasted: line count,
    dollar-sign count, memoryguard sites, and the number of object and data declarations. These
    are the numbers the header quotes and the ones a reader who cannot run solc can still check
    against the committed file. -/
def irArtifactShape_ok : IO Bool := do
  let t0 <- readIrArtifact verifierArtifactPath
  let t1 <- readIrArtifact vkArtifactPath
  pure ((t0.splitOn "\n").length == 2898 &&
    (t0.splitOn "$").length - 1 == 4580 &&
    (t0.splitOn "memoryguard").length - 1 == 2 &&
    (t0.splitOn "object \"").length - 1 == 2 &&
    (t0.splitOn "data \"").length - 1 == 1 &&
    (t1.splitOn "\n").length == 604 &&
    (t1.splitOn "$").length - 1 == 537 &&
    (t1.splitOn "memoryguard").length - 1 == 1 &&
    (t1.splitOn "object \"").length - 1 == 2 &&
    (t1.splitOn "data \"").length - 1 == 1)

#eval irArtifactShape_ok                    -- expect true

/-- GATE 4: DECISION 2, auditable. The rename rule re-derived from the artifact text by the
    Lean lexer: injective, no image colliding with a name the rule leaves alone, no image that
    is a Yul keyword or a reserved word, the rename non-trivial, and every rename reversible by
    dropping the prefix. -/
def irRename_ok : IO Bool := do
  let ids := ((irIdents (← readIrArtifact verifierArtifactPath)) ++
    (irIdents (← readIrArtifact vkArtifactPath))).eraseDups
  let imgs := ids.map irRen
  let renamed := ids.filter irNeedsRen
  let untouched := ids.filter (fun x => ! irNeedsRen x)
  pure (ids.length > 1000 &&
    -- injective on the artifact's identifier set
    imgs.eraseDups.length == ids.length &&
    -- no image collides with a name the rule leaves alone
    ! (untouched.any (fun x => renamed.any (fun y => irRen y == x))) &&
    -- no RENAMED image is a Yul keyword or a Lean reserved word (the untouched names are
    -- allowed to be keywords: that is what the grammar is for)
    ! ((renamed.map irRen).any (fun x => x == "if" || x == "let" || x == "for" ||
      x == "switch" || x == "case" || x == "default" || x == "function" || x == "leave" ||
      x == "object" || x == "code" || x == "data" || x == "break" || x == "continue" ||
      x == "end" || x == "return")) &&
    -- the rename is non-trivial: the artifacts really do carry these names
    renamed.length == 517 &&
    -- and the rule is reversible on every renamed name
    (renamed.all (fun x => irRen x == "solc_" ++ x.replace "$" "_" &&
      (irRen x).length == x.length + 5)))

#eval irRename_ok                             -- expect true

/-- GATE 5: no original name survives in the imported AST, and every renamed artifact name is
    actually present. The first conjunct catches a rename that was skipped; the second is the
    completeness direction of hazard 2 - a statement deleted to make the build pass takes its
    identifiers with it, and this goes red. -/
def irNoOriginalSurvives_ok : IO Bool := do
  let ns := objectNames verifierIr ++ objectNames vkIr
  let vr <- verifierRenamed
  let kr <- vkRenamed
  pure (ns.all (fun n => ! n.contains '$' && ! irReserved.contains n) &&
    vr.all (fun x => ns.contains (irRen x)) &&
    kr.all (fun x => ns.contains (irRen x)) &&
    -- the non-mechanical rename is exercised, not just the dollar-sign one
    ns.contains "solc_end" &&
    ns.length > 1000)

#eval irNoOriginalSurvives_ok               -- expect true

/-- GATE 6: THE ANTI-DROP GATE. Every builtin call site and every user-function site that the
    generator counted in the committed artifact text (Midfall/Yul/solc-ir-callsites.tsv, a regex
    over the text) is present in the imported AST with the same multiplicity, after the alpha-
    rename. Two independent routes to the same number - a python regex over the artifact and a
    fold over the elaborated term - and a deleted statement changes only one of them. This is
    what makes a partial import presented as a complete one a build failure. -/
def irCallSitesMatch_ok : IO Bool := do
  let rows := parseIrManifest (← readIrArtifact callsitesPath)
  let vbc := objectBuiltinCalls verifierIr
  let kbc := objectBuiltinCalls vkIr
  let vuc := objectUserCalls verifierIr
  let kuc := objectUserCalls vkIr
  let count (l : List String) (n : String) : Nat := (l.filter (fun x => x == n)).length
  let vrows := rows.filter fun r => r.artifact == "Halo2Verifier"
  let krows := rows.filter fun r => r.artifact == "Halo2VerifyingKey"
  pure ((vrows.filter fun r => r.kind == "builtin").length > 30 &&
        -- nothing unresolved: the dialect still parses every name the artifact calls
        (rows.filter fun r => r.kind == "unresolved").length == 0 &&
        (vrows.filter fun r => r.kind == "builtin").all fun r =>
          count vbc (irRen r.name) == r.sites &&
        (krows.filter fun r => r.kind == "builtin").all fun r =>
          count kbc (irRen r.name) == r.sites &&
        (vrows.filter fun r => r.kind == "user").all fun r =>
          count vuc (irRen r.name) == r.sites &&
        (krows.filter fun r => r.kind == "user").all fun r =>
          count kuc (irRen r.name) == r.sites &&
        -- and the check is not vacuous: the deployed verifier calls, through this import, the
        -- two builtins P-VEND added to the dialect
        count vbc "memoryguard" == 2 && count vbc "setimmutable" == 1 &&
        count vbc "loadimmutable" == 2 && count kbc "memoryguard" == 1)

#eval irCallSitesMatch_ok                 -- expect true

/-- GATE 9: A FINDING ABOUT THE TRACKED MANIFEST, pinned so it cannot be lost.
    Midfall/Yul/ir-builtins.tsv is not a measurement of the deployed Halo2Verifier artifact:
    scripts/extract_ir_builtins.py keys its standard-json source dict by BASENAME, and two of
    its three tracked sources are named Halo2Verifier.sol (the deployed one and the poseidon
    fixture dump), so the later entry overwrites the earlier and the rows labelled
    "Halo2Verifier" were computed from the poseidon dump. The deployed artifact has no xor site;
    the manifest claims three. This gate pins the divergence: fixing the collision and
    regenerating ir-builtins.tsv turns it red rather than leaving the story untold. It is a
    finding about that manifest, not about this import - gate 6 measures the committed artifact
    directly, and the two names P-VEND was actually about agree either way (last conjuncts). -/
def irBuiltinsManifestDiverges_ok : IO Bool := do
  let rows := parseIrManifest (← readIrManifest)
  let sites (art name : String) : Nat :=
    (rows.filter fun r => r.artifact == art && r.name == name).foldl (fun acc r => acc + r.sites) 0
  let vbc := objectBuiltinCalls verifierIr
  let count (l : List String) (n : String) : Nat := (l.filter (fun x => x == n)).length
  pure (count vbc "xor" == 0 && sites "Halo2Verifier" "xor" == 3 &&
    count vbc "memoryguard" == sites "Halo2Verifier" "memoryguard" &&
    count vbc "setimmutable" == sites "Halo2Verifier" "setimmutable" &&
    count vbc "loadimmutable" == sites "Halo2Verifier" "loadimmutable")

#eval irBuiltinsManifestDiverges_ok       -- expect true

/-- GATE 7: structural shape of the imported objects - names, sub-objects, data segments, and
    the elaborated node counts. The node counts are pinned from the AST this file elaborated to
    (gates 2 to 6 are what tie it to the artifact), so what they protect is a hand-edit of THIS
    file: any statement removed changes one of them. -/
def irShape_ok : Bool :=
  verifierIr.name == "Halo2Verifier_292" &&
    vkIr.name == "Halo2VerifyingKey_302" &&
    verifierIr.subObjects.map (fun o => o.name) == ["Halo2Verifier_292_deployed"] &&
    vkIr.subObjects.map (fun o => o.name) == ["Halo2VerifyingKey_302_deployed"] &&
    verifierIr.dataSegs.isEmpty && vkIr.dataSegs.isEmpty &&
    verifierRuntimeObject.dataSegs.map (fun d => d.1) == [".metadata"] &&
    vkRuntimeObject.dataSegs.map (fun d => d.1) == [".metadata"] &&
    ! verifierRuntime.isEmpty && ! vkRuntime.isEmpty &&
    objectStmtCount verifierIr == 5229 &&
    objectStmtCount vkIr == 1642 &&
    verifierRuntime.length == 28 &&
    vkRuntime.length == 5 &&
    (objectNames verifierIr).length == 5037 &&
    (objectNames vkIr).length == 558 &&
    -- the immutable pair is present in the imported object, not merely in the dialect
    importedSetImmutableSite.isSome && importedLoadImmutableSites == 2 &&
    -- and every identifier of the quotation, in order: this is what sees a local variable
    -- renamed, which neither the call-site gate nor the literal gate can see
    objectNameDigest verifierIr == (3939906383463826799 : UInt64) &&
    objectNameDigest vkIr == (15713202309330422114 : UInt64)

#eval irShape_ok                            -- expect true

/-- GATE 8: the imported runtime starts with the prologue the header says it starts with,
    checked against the quotation rather than against a hand-typed copy of it. -/
def irPrologueIsTheImportedHead : Bool :=
  SyntaxEq.stmtsBeq [verifierRuntime.head?.getD Stmt.leave]
    [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])] &&
  SyntaxEq.stmtsBeq [vkRuntime.head?.getD Stmt.leave]
    [Stmt.exprStmt (Expr.builtin Op.mstore
      [Expr.lit (.number 64), Expr.builtin Op.memoryguard [Expr.lit (.number 128)]])]

#eval irPrologueIsTheImportedHead         -- expect true

/-- GATE 10: the literals. The call-site gate sees names, not values, so a changed numeric
    literal - add(x, 1) rewritten to add(x, 2), or the memoryguard reservation edited - would
    pass it. The count and sum of every numeric literal, the count and total byte length of
    every string literal, and the count of boolean literals are pinned here for both objects. -/
def irLiterals_ok : Bool :=
  let a := objectLits verifierIr
  let b := objectLits vkIr
  a.numCount == 2068 && a.numSum == 1750937326901977666623612667226219455528541511728417536716929766574131469976978 && a.strCount == 8 &&
    a.strBytes == 108 && a.strSum == 10078 && a.boolCount == 1 &&
    b.numCount == 1079 && b.numSum == 16189178311403014548454539355588231629199032355268472819124059515527964270806584 && b.strCount == 3 &&
    b.strBytes == 90 && b.strSum == 8625 && b.boolCount == 0

#eval irLiterals_ok                         -- expect true

/-! ### Axiom audit -/

-- D-P15's checker is the elaborator, so the imported terms must carry no assumptions of
-- their own. Expected: [propext, Classical.choice, Quot.sound] - the three the quotation
-- macro leaves behind - and in particular NO sorryAx.
#print axioms Midfall.Yul.Ir.verifierIr
#print axioms Midfall.Yul.Ir.vkIr
#print axioms Midfall.Yul.Ir.verifierRuntime_head_is_memoryguard

end Midfall.Yul.Ir
-- GENERATED-BODY-ABOVE
