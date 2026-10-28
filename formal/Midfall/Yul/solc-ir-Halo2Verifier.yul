
/// @use-src 0:"Halo2Verifier.sol"
object "Halo2Verifier_292" {
    code {
        /// @src 0:2063:206619  "contract Halo2Verifier {..."
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
            // protect against overflow
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

        function abi_decode_t_address_fromMemory(offset, end) -> value {
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

        /// @src 0:2568:2620  "uint256 internal constant EXPECTED_VK_LENGTH = 17025"
        function constant_EXPECTED_VK_LENGTH_11() -> ret {
            /// @src 0:2615:2620  "17025"
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

        /// @src 0:2626:2746  "uint256 internal constant EXPECTED_VK_CODEHASH_WORD = 0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009"
        function constant_EXPECTED_VK_CODEHASH_WORD_14() -> ret {
            /// @src 0:2680:2746  "0x24430c63ec2017f12ec4004d66c66314f418dd77fe38dd4c2475c8f2b259e009"
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

        /// @src 0:2752:2835  "bytes32 internal constant EXPECTED_VK_CODEHASH = bytes32(EXPECTED_VK_CODEHASH_WORD)"
        function constant_EXPECTED_VK_CODEHASH_20() -> ret {
            /// @src 0:2809:2834  "EXPECTED_VK_CODEHASH_WORD"
            let expr_18 := constant_EXPECTED_VK_CODEHASH_WORD_14()
            /// @src 0:2801:2835  "bytes32(EXPECTED_VK_CODEHASH_WORD)"
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

        function abi_encode_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf_to_t_string_memory_ptr_fromStack(pos) -> end {
            pos := array_storeLengthForEncoding_t_string_memory_ptr_fromStack(pos, 10)
            store_literal_in_memory_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(pos)
            end := add(pos, 32)
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
                let end := abi_encode_tuple_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf__to_t_string_memory_ptr__fromStack(add(memPtr, 4) )
                revert(memPtr, sub(end, memPtr))
            }
        }

        /// @ast-id 273
        /// @src 0:15089:15560  "constructor(address authorizedVk) {..."
        function constructor_Halo2Verifier_292(var_authorizedVk_248) {

            /// @src 0:15089:15560  "constructor(address authorizedVk) {..."

            fun_require_eip2537_precompiles_245()
            /// @src 0:15368:15380  "authorizedVk"
            let _3 := var_authorizedVk_248
            let expr_255 := _3
            /// @src 0:15368:15392  "authorizedVk.code.length"
            let expr_257 := extcodesize(expr_255)
            /// @src 0:15396:15414  "EXPECTED_VK_LENGTH"
            let expr_258 := constant_EXPECTED_VK_LENGTH_11()
            /// @src 0:15368:15414  "authorizedVk.code.length == EXPECTED_VK_LENGTH"
            let expr_259 := eq(cleanup_t_uint256(expr_257), cleanup_t_uint256(expr_258))
            /// @src 0:15368:15479  "authorizedVk.code.length == EXPECTED_VK_LENGTH..."
            let expr_264 := expr_259
            if expr_264 {
                /// @src 0:15434:15446  "authorizedVk"
                let _5 := var_authorizedVk_248
                let expr_260 := _5
                /// @src 0:15434:15455  "authorizedVk.codehash"
                let expr_261 := extcodehash(expr_260)
                /// @src 0:15459:15479  "EXPECTED_VK_CODEHASH"
                let expr_262 := constant_EXPECTED_VK_CODEHASH_20()
                /// @src 0:15434:15479  "authorizedVk.codehash == EXPECTED_VK_CODEHASH"
                let expr_263 := eq(cleanup_t_bytes32(expr_261), cleanup_t_bytes32(expr_262))
                /// @src 0:15368:15479  "authorizedVk.code.length == EXPECTED_VK_LENGTH..."
                expr_264 := expr_263
            }
            /// @src 0:15347:15515  "require(..."
            require_helper_t_stringliteral_fe83574233e00b8a11546c4c46372241e16886722a6440d7b1ddfd49f86ecedf(expr_264)
            /// @src 0:15541:15553  "authorizedVk"
            let _8 := var_authorizedVk_248
            let expr_269 := _8
            /// @src 0:15525:15553  "AUTHORIZED_VK = authorizedVk"
            let _9 := expr_269
            mstore(128, _9)
            let expr_270 := expr_269

        }
        /// @src 0:2063:206619  "contract Halo2Verifier {..."

        /// @ast-id 245
        /// @src 0:11991:14825  "function require_eip2537_precompiles() private view {..."
        function fun_require_eip2537_precompiles_245() {

            /// @src 0:12053:14819  "assembly (\"memory-safe\") {..."
            {
                let usr$scratch := 0x80
                mstore(usr$scratch, 0x1234)
                mcopy(add(usr$scratch, 0x20), usr$scratch, 0x20)
                if iszero(eq(mload(add(usr$scratch, 0x20)), 0x1234)) { revert(0, 0) }
                for { let usr$off := 0 }
                lt(usr$off, 0x0300)
                { usr$off := add(usr$off, 0x20) }
                {
                    mstore(add(usr$scratch, usr$off), 0)
                }
                if iszero(staticcall(gas(), 0x0b, usr$scratch, 0x0100, usr$scratch, 0x80)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
                if or(or(mload(usr$scratch), mload(add(usr$scratch, 0x20))), or(mload(add(usr$scratch, 0x40)), mload(add(usr$scratch, 0x60)))) { revert(0, 0) }
                let usr$msm_scratch := 0xa1c0
                for { let usr$off := 0 }
                lt(usr$off, 0x30c0)
                { usr$off := add(usr$off, 0x20) }
                {
                    mstore(add(usr$msm_scratch, usr$off), 0)
                }
                if iszero(staticcall(gas(), 0x0c, usr$msm_scratch, 0x30c0, usr$scratch, 0x80)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x80)) { revert(0, 0) }
                if or(or(mload(usr$scratch), mload(add(usr$scratch, 0x20))), or(mload(add(usr$scratch, 0x40)), mload(add(usr$scratch, 0x60)))) { revert(0, 0) }
                if iszero(staticcall(gas(), 0x0f, usr$scratch, 0x0300, usr$scratch, 0x20)) { revert(0, 0) }
                if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
                if iszero(eq(mload(usr$scratch), 1)) { revert(0, 0) }
            }

        }
        /// @src 0:2063:206619  "contract Halo2Verifier {..."

    }
    /// @use-src 0:"Halo2Verifier.sol"
    object "Halo2Verifier_292_deployed" {
        code {
            /// @src 0:2063:206619  "contract Halo2Verifier {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x1e8e1e13
                {
                    // verifyProof(bytes,uint256[])

                    external_fun_verifyProof_291()
                }

                case 0x42b72597
                {
                    // AUTHORIZED_VK()

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

            // bytes
            function abi_decode_t_bytes_calldata_ptr(offset, end) -> arrayPos, length {
                if iszero(slt(add(offset, 0x1f), end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x01)), end) { revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() }
            }

            // uint256[]
            function abi_decode_t_array$_t_uint256_$dyn_calldata_ptr(offset, end) -> arrayPos, length {
                if iszero(slt(add(offset, 0x1f), end)) { revert_error_1b9f4a0a5773e33b91aa01db23bf8c55fce1411167c872835e7fa00a4f17d46d() }
                length := calldataload(offset)
                if gt(length, 0xffffffffffffffff) { revert_error_15abf5612cd996bc235ba1e55a4a30ac60e6bb601ff7ba4ad3f179b6be8d0490() }
                arrayPos := add(offset, 0x20)
                if gt(add(arrayPos, mul(length, 0x20)), end) { revert_error_81385d8c0b31fffe14be1da910c8bd3a80be4cfa248e04f42ec0faea3132a8ef() }
            }

            function abi_decode_tuple_t_bytes_calldata_ptrt_array$_t_uint256_$dyn_calldata_ptr(headStart, dataEnd) -> value0, value1, value2, value3 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := calldataload(add(headStart, 0))
                    if gt(offset, 0xffffffffffffffff) { revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() }

                    value0, value1 := abi_decode_t_bytes_calldata_ptr(add(headStart, offset), dataEnd)
                }

                {

                    let offset := calldataload(add(headStart, 32))
                    if gt(offset, 0xffffffffffffffff) { revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() }

                    value2, value3 := abi_decode_t_array$_t_uint256_$dyn_calldata_ptr(add(headStart, offset), dataEnd)
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
                let param_0, param_1, param_2, param_3 :=  abi_decode_tuple_t_bytes_calldata_ptrt_array$_t_uint256_$dyn_calldata_ptr(4, calldatasize())
                let ret_0 :=  fun_verifyProof_291(param_0, param_1, param_2, param_3)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_bool__to_t_bool__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            /// @ast-id 5
            /// @src 0:2283:2321  "address public immutable AUTHORIZED_VK"
            function getter_fun_AUTHORIZED_VK_5() -> rval {

                rval := loadimmutable("5")

            }
            /// @src 0:2063:206619  "contract Halo2Verifier {..."

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

            /// @ast-id 291
            /// @src 0:17140:206617  "function verifyProof(..."
            function fun_verifyProof_291(var_proof_276_offset, var_proof_276_length, var_instances_279_offset, var_instances_279_length) -> var__282 {
                /// @src 0:17258:17262  "bool"
                let zero_t_bool_1 := zero_value_for_split_t_bool()
                var__282 := zero_t_bool_1

                /// @src 0:17681:17873  "assembly (\"memory-safe\") {..."
                {
                    if iszero(and(eq(calldataload(0x04), 0x40), eq(calldataload(0x24), sub(7876, 0x04)))) { revert(0, 0) }
                }
                /// @src 0:18094:18107  "AUTHORIZED_VK"
                let _2 := loadimmutable("5")
                let expr_287 := _2
                /// @src 0:18081:18107  "address vk = AUTHORIZED_VK"
                let var_vk_286 := expr_287
                /// @src 0:18117:206611  "assembly (\"memory-safe\") {..."
                {
                    function usr$scalar_inv(usr$x) -> usr$inv
                    {
                        if iszero(usr$x) { revert(0, 0) }
                        let usr$p := 0x2600
                        mstore(add(usr$p, 0x00), 0x20)
                        mstore(add(usr$p, 0x20), 0x20)
                        mstore(add(usr$p, 0x40), 0x20)
                        mstore(add(usr$p, 0x60), usr$x)
                        mstore(add(usr$p, 0x80), sub(52435875175126190479447740508185965837690552500527637822603658699938581184513, 2))
                        mstore(add(usr$p, 0xa0), 52435875175126190479447740508185965837690552500527637822603658699938581184513)
                        if iszero(staticcall(gas(), 0x05, usr$p, 0xc0, usr$p, 0x20)) { revert(0, 0) }
                        if iszero(eq(returndatasize(), 0x20)) { revert(0, 0) }
                        usr$inv := mload(usr$p)
                    }
                    function usr$transcript_init() -> usr$buf_len
                    { usr$buf_len := 128 }
                    function usr$common_word(usr$buf_len, usr$word) -> usr$ret
                    {
                        mstore(usr$buf_len, usr$word)
                        usr$ret := add(usr$buf_len, 32)
                    }
                    function usr$common_uncompressed_g1(usr$buf_len, usr$cptr) -> usr$ret
                    {
                        let usr$x_hi_word := calldataload(usr$cptr)
                        let usr$x_lo := calldataload(add(usr$cptr, 0x20))
                        let usr$y_hi_word := calldataload(add(usr$cptr, 0x40))
                        let usr$y_lo := calldataload(add(usr$cptr, 0x60))
                        if shr(128, usr$x_hi_word) { revert(0, 0) }
                        if shr(128, usr$y_hi_word) { revert(0, 0) }
                        let usr$x_hi := and(usr$x_hi_word, 0xffffffffffffffffffffffffffffffff)
                        let usr$y_hi := and(usr$y_hi_word, 0xffffffffffffffffffffffffffffffff)
                        if iszero(or(lt(usr$x_hi, 34565483545414906068789196026815425751), and(eq(usr$x_hi, 34565483545414906068789196026815425751), iszero(gt(usr$x_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))))) { revert(0, 0) }
                        if iszero(or(lt(usr$y_hi, 34565483545414906068789196026815425751), and(eq(usr$y_hi, 34565483545414906068789196026815425751), iszero(gt(usr$y_lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))))) { revert(0, 0) }
                        calldatacopy(usr$buf_len, usr$cptr, 0x80)
                        usr$ret := add(usr$buf_len, 0x80)
                    }
                    function usr$squeeze_to(usr$buf_len, usr$mptr) -> usr$ret
                    {
                        let usr$h0 := keccak256(128, sub(usr$buf_len, 128))
                        mstore(128, usr$h0)
                        let usr$r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                        mstore(usr$mptr, mod(usr$h0, usr$r))
                        usr$ret := add(128, 32)
                    }
                    function usr$batch_invert(usr$success, usr$mptr_start, usr$mptr_end, usr$scratch_mptr, usr$r) -> usr$ret
                    {
                        usr$ret := usr$success
                        if iszero(usr$ret) { leave }
                        if lt(usr$mptr_end, usr$mptr_start)
                        {
                            usr$ret := 0
                            leave
                        }
                        let usr$count_bytes := sub(usr$mptr_end, usr$mptr_start)
                        if iszero(usr$count_bytes) { leave }
                        if eq(usr$count_bytes, 0x20)
                        {
                            let usr$x := mload(usr$mptr_start)
                            if iszero(usr$x)
                            {
                                usr$ret := 0
                                leave
                            }
                            let usr$single_scratch := usr$scratch_mptr
                            mstore(add(usr$single_scratch, 0x00), 0x20)
                            mstore(add(usr$single_scratch, 0x20), 0x20)
                            mstore(add(usr$single_scratch, 0x40), 0x20)
                            mstore(add(usr$single_scratch, 0x60), usr$x)
                            mstore(add(usr$single_scratch, 0x80), sub(usr$r, 2))
                            mstore(add(usr$single_scratch, 0xa0), usr$r)
                            usr$ret := staticcall(gas(), 0x05, usr$single_scratch, 0xc0, usr$single_scratch, 0x20)
                            usr$ret := and(usr$ret, eq(returndatasize(), 0x20))
                            if usr$ret
                            {
                                mstore(usr$mptr_start, mload(usr$single_scratch))
                            }
                            leave
                        }
                        let usr$gp_mptr := usr$scratch_mptr
                        let usr$gp := mload(usr$mptr_start)
                        let usr$mptr := add(usr$mptr_start, 0x20)
                        for { } lt(usr$mptr, sub(usr$mptr_end, 0x20)) { }
                        {
                            usr$gp := mulmod(usr$gp, mload(usr$mptr), usr$r)
                            mstore(usr$gp_mptr, usr$gp)
                            usr$mptr := add(usr$mptr, 0x20)
                            usr$gp_mptr := add(usr$gp_mptr, 0x20)
                        }
                        usr$gp := mulmod(usr$gp, mload(usr$mptr), usr$r)
                        if iszero(usr$gp)
                        {
                            usr$ret := 0
                            leave
                        }
                        mstore(add(usr$gp_mptr, 0x00), 0x20)
                        mstore(add(usr$gp_mptr, 0x20), 0x20)
                        mstore(add(usr$gp_mptr, 0x40), 0x20)
                        mstore(add(usr$gp_mptr, 0x60), usr$gp)
                        mstore(add(usr$gp_mptr, 0x80), sub(usr$r, 2))
                        mstore(add(usr$gp_mptr, 0xa0), usr$r)
                        usr$ret := staticcall(gas(), 0x05, usr$gp_mptr, 0xc0, usr$gp_mptr, 0x20)
                        usr$ret := and(usr$ret, eq(returndatasize(), 0x20))
                        let usr$all_inv := mload(usr$gp_mptr)
                        let usr$first_mptr := usr$mptr_start
                        let usr$second_mptr := add(usr$first_mptr, 0x20)
                        usr$gp_mptr := sub(usr$gp_mptr, 0x20)
                        for { } lt(usr$second_mptr, usr$mptr) { }
                        {
                            let usr$inv := mulmod(usr$all_inv, mload(usr$gp_mptr), usr$r)
                            usr$all_inv := mulmod(usr$all_inv, mload(usr$mptr), usr$r)
                            mstore(usr$mptr, usr$inv)
                            usr$mptr := sub(usr$mptr, 0x20)
                            usr$gp_mptr := sub(usr$gp_mptr, 0x20)
                        }
                        let usr$inv_first := mulmod(usr$all_inv, mload(usr$second_mptr), usr$r)
                        let usr$inv_second := mulmod(usr$all_inv, mload(usr$first_mptr), usr$r)
                        mstore(usr$first_mptr, usr$inv_first)
                        mstore(usr$second_mptr, usr$inv_second)
                    }
                    function usr$ec_pairing(usr$success, usr$lhs_mptr, usr$rhs_mptr) -> usr$ret
                    {
                        usr$ret := usr$success
                        if iszero(usr$ret) { leave }
                        let usr$scratch := 0x0300
                        mcopy(usr$scratch, usr$lhs_mptr, 0x80)
                        mcopy(add(usr$scratch, 0x80), 10464, 0x100)
                        mcopy(add(usr$scratch, 0x180), usr$rhs_mptr, 0x80)
                        mcopy(add(usr$scratch, 0x200), 10720, 0x100)
                        usr$ret := staticcall(gas(), 0x0f, usr$scratch, 0x0300, usr$scratch, 0x20)
                        usr$ret := and(usr$ret, eq(returndatasize(), 0x20))
                        usr$ret := and(usr$ret, mload(usr$scratch))
                        if iszero(usr$ret) { revert(0, 0) }
                        usr$ret := 1
                    }
                    function usr$load_acc_coord_shifted(usr$src, usr$bits, usr$n, usr$base, usr$limbs_per_word, usr$first_adjust) -> usr$hi, usr$lo
                    {
                        let usr$mask := sub(usr$base, 1)
                        for { let usr$i := 0 }
                        lt(usr$i, usr$n)
                        { usr$i := add(usr$i, 1) }
                        {
                            let usr$packed := calldataload(add(usr$src, mul(div(usr$i, usr$limbs_per_word), 0x20)))
                            if and(iszero(div(usr$i, usr$limbs_per_word)), usr$first_adjust)
                            {
                                usr$packed := sub(usr$packed, usr$first_adjust)
                            }
                            let usr$limb := and(shr(mul(mod(usr$i, usr$limbs_per_word), usr$bits), usr$packed), usr$mask)
                            let usr$shift := mul(usr$i, usr$bits)
                            if lt(usr$shift, 256)
                            {
                                usr$lo := add(usr$lo, shl(usr$shift, usr$limb))
                                if gt(add(usr$shift, usr$bits), 256)
                                {
                                    usr$hi := add(usr$hi, shr(sub(256, usr$shift), usr$limb))
                                }
                            }
                            if iszero(lt(usr$shift, 256))
                            {
                                usr$hi := add(usr$hi, shl(sub(usr$shift, 256), usr$limb))
                            }
                        }
                    }
                    function usr$is_bls_p_minus_one(usr$hi, usr$lo) -> usr$yes
                    {
                        usr$yes := and(eq(usr$hi, 34565483545414906068789196026815425751), eq(usr$lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850))
                    }
                    function usr$is_acc_encoded_identity(usr$src) -> usr$yes
                    {
                        usr$yes := and(and(eq(calldataload(usr$src), 25645630028331783532722944590531249665523018521732485735708912233130), eq(calldataload(add(usr$src, 0x20)), 148457621397983152316361523253305392630546779012)), and(eq(calldataload(add(usr$src, 0x40)), 25645630028331783532722944590531249665523018521732413678114874305194), eq(calldataload(add(usr$src, 0x60)), 148457621397983152316361523253305392630546779012)))
                    }
                    function usr$check_acc_coord_packing(usr$src, usr$bits, usr$n, usr$limbs_per_word) -> usr$ok
                    {
                        usr$ok := 1
                        let usr$coord_words := div(add(usr$n, sub(usr$limbs_per_word, 1)), usr$limbs_per_word)
                        for { let usr$word_idx := 0 }
                        lt(usr$word_idx, usr$coord_words)
                        {
                            usr$word_idx := add(usr$word_idx, 1)
                        }
                        {
                            let usr$remaining := sub(usr$n, mul(usr$word_idx, usr$limbs_per_word))
                            let usr$limbs_in_word := usr$limbs_per_word
                            if lt(usr$remaining, usr$limbs_per_word)
                            {
                                usr$limbs_in_word := usr$remaining
                            }
                            let usr$used_bits := mul(usr$limbs_in_word, usr$bits)
                            if lt(usr$used_bits, 256)
                            {
                                usr$ok := and(usr$ok, lt(calldataload(add(usr$src, mul(usr$word_idx, 0x20))), shl(usr$used_bits, 1)))
                            }
                        }
                    }
                    function usr$load_acc_coord(usr$src, usr$allow_id, usr$bits, usr$n, usr$base, usr$limbs_per_word) -> usr$ok, usr$hi, usr$lo, usr$is_id
                    {
                        usr$ok := usr$check_acc_coord_packing(usr$src, usr$bits, usr$n, usr$limbs_per_word)
                        if and(usr$allow_id, iszero(lt(calldataload(usr$src), usr$base)))
                        {
                            let usr$adj_hi, usr$adj_lo := usr$load_acc_coord_shifted(usr$src, usr$bits, usr$n, usr$base, usr$limbs_per_word, usr$base)
                            usr$is_id := usr$is_bls_p_minus_one(usr$adj_hi, usr$adj_lo)
                        }
                        usr$hi, usr$lo := usr$load_acc_coord_shifted(usr$src, usr$bits, usr$n, usr$base, usr$limbs_per_word, mul(usr$is_id, usr$base))
                        usr$ok := and(usr$ok, or(lt(usr$hi, 34565483545414906068789196026815425751), and(eq(usr$hi, 34565483545414906068789196026815425751), iszero(gt(usr$lo, 45442060874369865957053122457065728162598490762543039060009208264153100167850)))))
                        let usr$was_p_minus_one := usr$is_bls_p_minus_one(usr$hi, usr$lo)
                        if usr$was_p_minus_one
                        {
                            usr$hi := 0
                            usr$lo := 0
                        }
                        if iszero(usr$was_p_minus_one)
                        {
                            let usr$next_lo := add(usr$lo, 1)
                            usr$hi := add(usr$hi, lt(usr$next_lo, usr$lo))
                            usr$lo := usr$next_lo
                        }
                        usr$ok := and(usr$ok, lt(usr$hi, shl(128, 1)))
                    }
                    function usr$load_acc_point(usr$dst, usr$src, usr$bits, usr$n, usr$base) -> usr$ok, usr$is_id
                    {
                        usr$is_id := usr$is_acc_encoded_identity(usr$src)
                        if usr$is_id
                        {
                            usr$ok := 1
                            mstore(usr$dst, 0)
                            mstore(add(usr$dst, 0x20), 0)
                            mstore(add(usr$dst, 0x40), 0)
                            mstore(add(usr$dst, 0x60), 0)
                        }
                        if iszero(usr$is_id)
                        {
                            let usr$limbs_per_word := 4
                            let usr$coord_words := div(add(usr$n, sub(usr$limbs_per_word, 1)), usr$limbs_per_word)
                            let usr$x_ok, usr$x_hi, usr$x_lo, usr$x_is_id := usr$load_acc_coord(usr$src, 1, usr$bits, usr$n, usr$base, usr$limbs_per_word)
                            let usr$y_ok, usr$y_hi, usr$y_lo, usr$y_id := usr$load_acc_coord(add(usr$src, mul(usr$coord_words, 0x20)), 0, usr$bits, usr$n, usr$base, usr$limbs_per_word)
                            pop(usr$y_id)
                            usr$ok := and(usr$x_ok, usr$y_ok)
                            usr$is_id := usr$x_is_id
                            if usr$is_id
                            {
                                usr$ok := and(usr$ok, iszero(or(or(usr$x_hi, usr$x_lo), or(usr$y_hi, usr$y_lo))))
                                mstore(usr$dst, 0)
                                mstore(add(usr$dst, 0x20), 0)
                                mstore(add(usr$dst, 0x40), 0)
                                mstore(add(usr$dst, 0x60), 0)
                            }
                            if iszero(usr$is_id)
                            {
                                let usr$decoded_zero := iszero(or(or(usr$x_hi, usr$x_lo), or(usr$y_hi, usr$y_lo)))
                                usr$ok := and(usr$ok, iszero(usr$decoded_zero))
                                mstore(usr$dst, usr$x_hi)
                                mstore(add(usr$dst, 0x20), usr$x_lo)
                                mstore(add(usr$dst, 0x40), usr$y_hi)
                                mstore(add(usr$dst, 0x60), usr$y_lo)
                            }
                        }
                    }
                    function usr$validate_public_accumulator(usr$success, usr$r) -> usr$out
                    {
                        usr$out := usr$success
                        let usr$bits := 56
                        let usr$n := 7
                        let usr$limb_base := shl(usr$bits, 1)
                        let usr$limbs_per_word := 4
                        let usr$coord_words := div(add(usr$n, sub(usr$limbs_per_word, 1)), usr$limbs_per_word)
                        let usr$acc_instance_ptr := add(7908, 0x0160)
                        let usr$lhs_scalar_ptr := add(usr$acc_instance_ptr, mul(mul(2, usr$coord_words), 0x20))
                        let usr$lhs_ok, usr$lhs_is_id := usr$load_acc_point(27584, usr$acc_instance_ptr, usr$bits, usr$n, usr$limb_base)
                        usr$out := and(usr$out, usr$lhs_ok)
                        let usr$acc_scratch := 0xa1c0
                        {
                            let usr$lhs_scalar := 1
                            pop(usr$lhs_is_id)
                            mcopy(usr$acc_scratch, 27584, 0x80)
                            mstore(add(usr$acc_scratch, 0x80), usr$lhs_scalar)
                            if usr$out
                            {
                                usr$out := staticcall(gas(), 0x0c, usr$acc_scratch, 0xa0, 27584, 0x80)
                                usr$out := and(usr$out, eq(returndatasize(), 0x80))
                            }
                        }
                        let usr$rhs_instance_ptr := usr$lhs_scalar_ptr
                        let usr$rhs_scalar_ptr := add(usr$rhs_instance_ptr, mul(mul(2, usr$coord_words), 0x20))
                        let usr$rhs_ok, usr$rhs_is_id := usr$load_acc_point(27712, usr$rhs_instance_ptr, usr$bits, usr$n, usr$limb_base)
                        usr$out := and(usr$out, usr$rhs_ok)
                        let usr$acc_pair_ptr := usr$acc_scratch
                        {
                            let usr$rhs_scalar := 1
                            pop(usr$rhs_is_id)
                            mcopy(usr$acc_pair_ptr, 27712, 0x80)
                            mstore(add(usr$acc_pair_ptr, 0x80), usr$rhs_scalar)
                            usr$acc_pair_ptr := add(usr$acc_pair_ptr, 0xa0)
                        }
                        let usr$acc_msm_len := sub(usr$acc_pair_ptr, usr$acc_scratch)
                        if usr$acc_msm_len
                        {
                            if usr$out
                            {
                                usr$out := staticcall(gas(), 0x0c, usr$acc_scratch, usr$acc_msm_len, 27712, 0x80)
                                usr$out := and(usr$out, eq(returndatasize(), 0x80))
                            }
                        }
                    }
                    let usr$r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                    let usr$success := true
                    {
                        if iszero(and(eq(extcodesize(var_vk_286), 17025), eq(extcodehash(var_vk_286), 16401726817195526609941831384088918008201368669469322348229147391391451176969))) { revert(0, 0) }
                        extcodecopy(var_vk_286, 9984, 0x01, 17024)
                        usr$success := and(usr$success, eq(mload(10016), 19))
                        usr$success := and(usr$success, eq(mload(10048), 20))
                        usr$success := and(usr$success, eq(mload(10208), 1))
                        usr$success := and(usr$success, eq(mload(10240), 11))
                        usr$success := and(usr$success, eq(mload(10272), 7))
                        usr$success := and(usr$success, eq(mload(10304), 56))
                        if iszero(usr$success) { revert(0, 0) }
                        usr$success := and(usr$success, eq(0x1e60, calldataload(68)))
                        usr$success := and(usr$success, eq(19, calldataload(7876)))
                        usr$success := and(usr$success, eq(calldatasize(), add(7908, 0x0260)))
                        if iszero(usr$success) { revert(0, 0) }
                    }
                    usr$success := usr$validate_public_accumulator(usr$success, usr$r)
                    if iszero(usr$success) { revert(0, 0) }
                    let usr$buf_len := usr$transcript_init()
                    usr$buf_len := usr$common_word(usr$buf_len, mload(9984))
                    {
                        mstore(usr$buf_len, 0)
                        mstore(add(usr$buf_len, 0x20), 0)
                        mstore(add(usr$buf_len, 0x40), 0)
                        mstore(add(usr$buf_len, 0x60), 0)
                        usr$buf_len := add(usr$buf_len, 0x80)
                    }
                    {
                        usr$buf_len := usr$common_word(usr$buf_len, 19)
                        let usr$instance_cptr := 7908
                        for {
                            let usr$instance_cptr_end := add(usr$instance_cptr, 0x0260)
                        }
                        lt(usr$instance_cptr, usr$instance_cptr_end)
                        {
                            usr$instance_cptr := add(usr$instance_cptr, 0x20)
                        }
                        {
                            let usr$inst_be := calldataload(usr$instance_cptr)
                            usr$success := and(usr$success, lt(usr$inst_be, usr$r))
                            usr$buf_len := usr$common_word(usr$buf_len, usr$inst_be)
                        }
                        if iszero(usr$success) { revert(0, 0) }
                    }
                    let usr$proof_cptr := 100
                    let usr$advice_walk := 37312
                    for {
                        let usr$end := add(usr$proof_cptr, 0x0780)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$advice_walk, usr$proof_cptr, 0x80)
                        usr$advice_walk := add(usr$advice_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27008)
                    let usr$lookup_m_walk := 39232
                    for {
                        let usr$end := add(usr$proof_cptr, 0x0100)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$lookup_m_walk, usr$proof_cptr, 0x80)
                        usr$lookup_m_walk := add(usr$lookup_m_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27040)
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27072)
                    let usr$perm_z_walk := 39488
                    for {
                        let usr$end := add(usr$proof_cptr, 0x0300)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$perm_z_walk, usr$proof_cptr, 0x80)
                        usr$perm_z_walk := add(usr$perm_z_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    let usr$lookup_helper_walk := 40256
                    let usr$lookup_z_walk := 40512
                    for {
                        let usr$end := add(usr$proof_cptr, 0x80)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$lookup_helper_walk, usr$proof_cptr, 0x80)
                        usr$lookup_helper_walk := add(usr$lookup_helper_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                    calldatacopy(usr$lookup_z_walk, usr$proof_cptr, 0x80)
                    usr$lookup_z_walk := add(usr$lookup_z_walk, 0x80)
                    usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    for {
                        let usr$end := add(usr$proof_cptr, 0x80)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$lookup_helper_walk, usr$proof_cptr, 0x80)
                        usr$lookup_helper_walk := add(usr$lookup_helper_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                    calldatacopy(usr$lookup_z_walk, usr$proof_cptr, 0x80)
                    usr$lookup_z_walk := add(usr$lookup_z_walk, 0x80)
                    usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27104)
                    let usr$trashcan_walk := 40768
                    for {
                        let usr$end := add(usr$proof_cptr, 0x80)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$trashcan_walk, usr$proof_cptr, 0x80)
                        usr$trashcan_walk := add(usr$trashcan_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27136)
                    let usr$quotient_walk := 40896
                    for {
                        let usr$end := add(usr$proof_cptr, 0x0200)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                        calldatacopy(usr$quotient_walk, usr$proof_cptr, 0x80)
                        usr$quotient_walk := add(usr$quotient_walk, 0x80)
                        usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27168)
                    {
                        let usr$eval_buf := 34048
                        for {
                            let usr$end := add(usr$proof_cptr, 0x0cc0)
                        }
                        lt(usr$proof_cptr, usr$end)
                        { }
                        {
                            let usr$eval := calldataload(usr$proof_cptr)
                            if iszero(lt(usr$eval, usr$r)) { revert(0, 0) }
                            mstore(usr$eval_buf, usr$eval)
                            usr$eval_buf := add(usr$eval_buf, 0x20)
                            usr$buf_len := usr$common_word(usr$buf_len, usr$eval)
                            usr$proof_cptr := add(usr$proof_cptr, 0x20)
                        }
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27200)
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27232)
                    usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                    calldatacopy(27328, usr$proof_cptr, 0x80)
                    usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27264)
                    mstore(27264, and(mload(27264), 0xffffffffffffffffffffffffffffffff))
                    mstore(33440, usr$proof_cptr)
                    for {
                        let usr$end := add(usr$proof_cptr, 0xa0)
                    }
                    lt(usr$proof_cptr, usr$end)
                    { }
                    {
                        let usr$eval := calldataload(usr$proof_cptr)
                        if iszero(lt(usr$eval, usr$r)) { revert(0, 0) }
                        usr$buf_len := usr$common_word(usr$buf_len, usr$eval)
                        usr$proof_cptr := add(usr$proof_cptr, 0x20)
                    }
                    usr$buf_len := usr$squeeze_to(usr$buf_len, 27296)
                    usr$buf_len := usr$common_uncompressed_g1(usr$buf_len, usr$proof_cptr)
                    calldatacopy(27456, usr$proof_cptr, 0x80)
                    usr$proof_cptr := add(usr$proof_cptr, 0x80)
                    if iszero(eq(usr$proof_cptr, 7876)) { revert(0, 0) }
                    if iszero(usr$success) { revert(0, 0) }
                    {
                        let usr$k := 20
                        let usr$x := mload(27168)
                        let usr$x_n := usr$x
                        for { let usr$idx := 0 }
                        lt(usr$idx, usr$k)
                        { usr$idx := add(usr$idx, 1) }
                        {
                            usr$x_n := mulmod(usr$x_n, usr$x_n, usr$r)
                        }
                        let usr$omega := mload(10112)
                        let usr$mptr := 27840
                        let usr$mptr_end := add(usr$mptr, 0x03a0)
                        for {
                            let usr$pow_of_omega := mload(10176)
                        }
                        lt(usr$mptr, usr$mptr_end)
                        {
                            usr$mptr := add(usr$mptr, 0x20)
                        }
                        {
                            mstore(usr$mptr, addmod(usr$x, sub(usr$r, usr$pow_of_omega), usr$r))
                            usr$pow_of_omega := mulmod(usr$pow_of_omega, usr$omega, usr$r)
                        }
                        let usr$x_n_minus_1 := addmod(usr$x_n, sub(usr$r, 1), usr$r)
                        mstore(usr$mptr_end, usr$x_n_minus_1)
                        usr$success := usr$batch_invert(usr$success, 27840, add(usr$mptr_end, 0x20), 41408, usr$r)
                        usr$mptr := 27840
                        let usr$l_i_common := mulmod(usr$x_n_minus_1, mload(10080), usr$r)
                        for {
                            let usr$pow_of_omega := mload(10176)
                        }
                        lt(usr$mptr, usr$mptr_end)
                        {
                            usr$mptr := add(usr$mptr, 0x20)
                        }
                        {
                            mstore(usr$mptr, mulmod(usr$l_i_common, mulmod(mload(usr$mptr), usr$pow_of_omega, usr$r), usr$r))
                            usr$pow_of_omega := mulmod(usr$pow_of_omega, usr$omega, usr$r)
                        }
                        let usr$l_blind := mload(add(27840, 0x20))
                        let usr$l_i_cptr := add(27840, 0x40)
                        for {
                            let usr$l_i_cptr_end := add(27840, 0x0140)
                        }
                        lt(usr$l_i_cptr, usr$l_i_cptr_end)
                        {
                            usr$l_i_cptr := add(usr$l_i_cptr, 0x20)
                        }
                        {
                            usr$l_blind := addmod(usr$l_blind, mload(usr$l_i_cptr), usr$r)
                        }
                        let usr$instance_eval := 0
                        for {
                            let usr$instance_cptr := 7908
                            let usr$instance_cptr_end := add(usr$instance_cptr, 0x0260)
                        }
                        lt(usr$instance_cptr, usr$instance_cptr_end)
                        {
                            usr$instance_cptr := add(usr$instance_cptr, 0x20)
                            usr$l_i_cptr := add(usr$l_i_cptr, 0x20)
                        }
                        {
                            usr$instance_eval := addmod(usr$instance_eval, mulmod(mload(usr$l_i_cptr), calldataload(usr$instance_cptr), usr$r), usr$r)
                        }
                        let usr$x_n_minus_1_inv := mload(usr$mptr_end)
                        let usr$l_last := mload(27840)
                        let usr$l_0 := mload(add(27840, 0x0140))
                        mstore(27840, usr$x_n)
                        mstore(27872, usr$x_n_minus_1_inv)
                        mstore(27904, usr$l_last)
                        mstore(27936, usr$l_blind)
                        mstore(27968, usr$l_0)
                        mstore(28000, usr$instance_eval)
                    }
                    if iszero(usr$success) { revert(0, 0) }
                    function usr$q_pow5(usr$x) -> usr$z
                    {
                        let usr$q_r := 52435875175126190479447740508185965837690552500527637822603658699938581184513
                        let usr$x2 := mulmod(usr$x, usr$x, usr$q_r)
                        usr$z := mulmod(usr$x, mulmod(usr$x2, usr$x2, usr$q_r), usr$q_r)
                    }
                    {
                        let usr$y := mload(27136)
                        let usr$q_const_mptr := 0x2ae0
                        let usr$q_program_mptr := 0x4120
                        mstore(0xa300, 0)
                        for { let usr$q_sel_zero_off := 0 }
                        lt(usr$q_sel_zero_off, 0x0140)
                        {
                            usr$q_sel_zero_off := add(usr$q_sel_zero_off, 0x20)
                        }
                        {
                            mstore(add(41408, usr$q_sel_zero_off), 0)
                        }
                        {
                            let usr$q_y_power := 1
                            for { let usr$q_y_power_i := 1 }
                            lt(usr$q_y_power_i, 49)
                            {
                                usr$q_y_power_i := add(usr$q_y_power_i, 1)
                            }
                            {
                                usr$q_y_power := mulmod(usr$q_y_power, usr$y, usr$r)
                                mstore(add(0xa340, shl(5, usr$q_y_power_i)), usr$q_y_power)
                            }
                        }
                        {
                            let usr$var0 := 0x1
                            let usr$f_3 := mload(0x8b40)
                            let usr$f_4 := mload(0x8a40)
                            let usr$a_0 := mload(0x8520)
                            let usr$var1 := mulmod(usr$f_4, usr$a_0, usr$r)
                            let usr$var2 := addmod(usr$f_3, usr$var1, usr$r)
                            let usr$f_5 := mload(0x8a60)
                            let usr$a_1 := mload(0x8540)
                            let usr$var3 := mulmod(usr$f_5, usr$a_1, usr$r)
                            let usr$var4 := addmod(usr$var2, usr$var3, usr$r)
                            let usr$f_6 := mload(0x8a80)
                            let usr$a_2 := mload(0x8560)
                            let usr$var5 := mulmod(usr$f_6, usr$a_2, usr$r)
                            let usr$var6 := addmod(usr$var4, usr$var5, usr$r)
                            let usr$f_7 := mload(0x8aa0)
                            let usr$a_3 := mload(0x8580)
                            let usr$var7 := mulmod(usr$f_7, usr$a_3, usr$r)
                            let usr$var8 := addmod(usr$var6, usr$var7, usr$r)
                            let usr$f_8 := mload(0x8ac0)
                            let usr$a_4 := mload(0x85a0)
                            let usr$var9 := mulmod(usr$f_8, usr$a_4, usr$r)
                            let usr$var10 := addmod(usr$var8, usr$var9, usr$r)
                            let usr$f_0 := mload(0x8ae0)
                            let usr$a_0_next_1 := mload(0x85c0)
                            let usr$var11 := mulmod(usr$f_0, usr$a_0_next_1, usr$r)
                            let usr$var12 := addmod(usr$var10, usr$var11, usr$r)
                            let usr$f_1 := mload(0x8b00)
                            let usr$var13 := mulmod(usr$f_1, usr$a_0, usr$r)
                            let usr$var14 := mulmod(usr$var13, usr$a_1, usr$r)
                            let usr$var15 := addmod(usr$var12, usr$var14, usr$r)
                            let usr$f_2 := mload(0x8b20)
                            let usr$var16 := mulmod(usr$f_2, usr$a_0, usr$r)
                            let usr$var17 := mulmod(usr$var16, usr$a_2, usr$r)
                            let usr$var18 := addmod(usr$var15, usr$var17, usr$r)
                            let usr$var19 := mulmod(usr$var0, usr$var18, usr$r)
                            mstore(0xa960, usr$var19)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                        {
                            let usr$q_selector_ptr := add(41408, 0x0)
                            let usr$q_selector_acc := mload(usr$q_selector_ptr)
                            mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                        }
                        {
                            let usr$var0 := 0x1
                            let usr$a_1 := mload(0x8540)
                            let usr$a_2 := mload(0x8560)
                            let usr$var1 := addmod(usr$a_1, usr$a_2, usr$r)
                            let usr$a_3 := mload(0x8580)
                            let usr$var2 := addmod(0, sub(usr$r, usr$a_3), usr$r)
                            let usr$var3 := addmod(usr$var1, usr$var2, usr$r)
                            let usr$a_4 := mload(0x85a0)
                            let usr$var4 := addmod(0, sub(usr$r, usr$a_4), usr$r)
                            let usr$var5 := addmod(usr$var3, usr$var4, usr$r)
                            let usr$var6 := mulmod(usr$var0, usr$var5, usr$r)
                            mstore(0xa960, usr$var6)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                        {
                            let usr$q_selector_ptr := add(41408, 0x20)
                            let usr$q_selector_acc := mload(usr$q_selector_ptr)
                            mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                        }
                        {
                            let usr$var0 := 0x1
                            let usr$a_0 := mload(0x8520)
                            let usr$f_4 := mload(0x8a40)
                            let usr$var1 := addmod(usr$a_0, usr$f_4, usr$r)
                            let usr$a_0_next_1 := mload(0x85c0)
                            let usr$var2 := addmod(0, sub(usr$r, usr$a_0_next_1), usr$r)
                            let usr$var3 := addmod(usr$var1, usr$var2, usr$r)
                            let usr$var4 := mulmod(usr$var0, usr$var3, usr$r)
                            mstore(0xa960, usr$var4)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                        {
                            let usr$q_selector_ptr := add(41408, 0x40)
                            let usr$q_selector_acc := mload(usr$q_selector_ptr)
                            mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                        }
                        {
                            let usr$var0 := 0x1
                            let usr$a_1 := mload(0x8540)
                            let usr$f_5 := mload(0x8a60)
                            let usr$var1 := addmod(usr$a_1, usr$f_5, usr$r)
                            let usr$a_1_next_1 := mload(0x85e0)
                            let usr$var2 := addmod(0, sub(usr$r, usr$a_1_next_1), usr$r)
                            let usr$var3 := addmod(usr$var1, usr$var2, usr$r)
                            let usr$var4 := mulmod(usr$var0, usr$var3, usr$r)
                            mstore(0xa960, usr$var4)
                        }
                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                        {
                            let usr$q_selector_ptr := add(41408, 0x40)
                            let usr$q_selector_acc := mload(usr$q_selector_ptr)
                            usr$q_selector_acc := mulmod(usr$q_selector_acc, mload(add(0xa340, 0x20)), usr$r)
                            mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                        }
                        let usr$q_pc := usr$q_program_mptr
                        let usr$q_end := add(usr$q_program_mptr, 0x11cf)
                        let usr$q_sp := 0xa960
                        let usr$q_top := 0
                        let usr$q_has_top := 0
                        for { } lt(usr$q_pc, usr$q_end) { }
                        {
                            let usr$q_op := byte(0, mload(usr$q_pc))
                            usr$q_pc := add(usr$q_pc, 1)
                            switch usr$q_op
                            case 0x05 {
                                let usr$q_ptr := shr(240, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 2)
                                if usr$q_has_top
                                {
                                    mstore(usr$q_sp, usr$q_top)
                                    usr$q_sp := add(usr$q_sp, 0x20)
                                }
                                usr$q_top := mload(usr$q_ptr)
                                usr$q_has_top := 1
                            }
                            case 0x06 {
                                usr$q_sp := sub(usr$q_sp, 0x20)
                                usr$q_top := addmod(mload(usr$q_sp), usr$q_top, usr$r)
                            }
                            case 0x08 {
                                usr$q_top := addmod(0, sub(usr$r, usr$q_top), usr$r)
                            }
                            case 0x0d {
                                let usr$qconst := byte(0, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 1)
                                usr$q_top := mulmod(usr$q_top, mload(add(usr$q_const_mptr, shl(5, usr$qconst))), usr$r)
                            }
                            case 0x10 {
                                let usr$q_ptr := shr(240, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 2)
                                usr$q_top := addmod(usr$q_top, mload(usr$q_ptr), usr$r)
                            }
                            case 0x11 {
                                let usr$q_ptr := shr(240, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 2)
                                usr$q_top := mulmod(usr$q_top, mload(usr$q_ptr), usr$r)
                            }
                            case 0x21 {
                                let usr$q_flags := byte(0, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 1)
                                let usr$q_cond_ptr := 0
                                if and(usr$q_flags, 0x01)
                                {
                                    usr$q_cond_ptr := shr(240, mload(usr$q_pc))
                                    usr$q_pc := add(usr$q_pc, 2)
                                }
                                let usr$q_acc := 0
                                if and(usr$q_flags, 0x02)
                                {
                                    let usr$qconst := byte(0, mload(usr$q_pc))
                                    usr$q_pc := add(usr$q_pc, 1)
                                    usr$q_acc := mload(add(usr$q_const_mptr, shl(5, usr$qconst)))
                                }
                                let usr$q_counts_word := mload(usr$q_pc)
                                let usr$q_lin_count := byte(0, usr$q_counts_word)
                                let usr$q_row_count := byte(1, usr$q_counts_word)
                                let usr$q_pairwise_count := byte(2, usr$q_counts_word)
                                let usr$q_mem_count := byte(3, usr$q_counts_word)
                                let usr$q_product_count := byte(4, usr$q_counts_word)
                                usr$q_pc := add(usr$q_pc, 5)
                                if usr$q_has_top
                                {
                                    mstore(usr$q_sp, usr$q_top)
                                    usr$q_sp := add(usr$q_sp, 0x20)
                                }
                                for { let usr$q_lin_block := 0 }
                                lt(usr$q_lin_block, usr$q_lin_count)
                                {
                                    usr$q_lin_block := add(usr$q_lin_block, 1)
                                }
                                {
                                    for { let usr$q_i := 0 }
                                    lt(usr$q_i, 7)
                                    { usr$q_i := add(usr$q_i, 1) }
                                    {
                                        let usr$q_word := mload(usr$q_pc)
                                        let usr$qconst := byte(0, usr$q_word)
                                        let usr$q_ptr := and(shr(232, usr$q_word), 0xffff)
                                        usr$q_pc := add(usr$q_pc, 3)
                                        usr$q_acc := addmod(usr$q_acc, mulmod(mload(add(usr$q_const_mptr, shl(5, usr$qconst))), mload(usr$q_ptr), usr$r), usr$r)
                                    }
                                }
                                for { let usr$q_row_block := 0 }
                                lt(usr$q_row_block, usr$q_row_count)
                                {
                                    usr$q_row_block := add(usr$q_row_block, 1)
                                }
                                {
                                    let usr$q_lhs := shr(240, mload(usr$q_pc))
                                    usr$q_pc := add(usr$q_pc, 2)
                                    let usr$q_lhs_value := mload(usr$q_lhs)
                                    for { let usr$q_i := 0 }
                                    lt(usr$q_i, 7)
                                    { usr$q_i := add(usr$q_i, 1) }
                                    {
                                        let usr$q_word := mload(usr$q_pc)
                                        let usr$qconst := byte(0, usr$q_word)
                                        let usr$q_rhs := and(shr(232, usr$q_word), 0xffff)
                                        usr$q_pc := add(usr$q_pc, 3)
                                        usr$q_acc := addmod(usr$q_acc, mulmod(mulmod(usr$q_lhs_value, mload(usr$q_rhs), usr$r), mload(add(usr$q_const_mptr, shl(5, usr$qconst))), usr$r), usr$r)
                                    }
                                }
                                for { let usr$q_pair_block := 0 }
                                lt(usr$q_pair_block, usr$q_pairwise_count)
                                {
                                    usr$q_pair_block := add(usr$q_pair_block, 1)
                                }
                                {
                                    let usr$q_pair_word := mload(usr$q_pc)
                                    let usr$q_lhs_base := shr(240, usr$q_pair_word)
                                    let usr$q_rhs_base := and(shr(224, usr$q_pair_word), 0xffff)
                                    usr$q_pc := add(usr$q_pc, 0x04)
                                    let usr$q_coeff_pc := usr$q_pc
                                    usr$q_pc := add(usr$q_pc, 13)
                                    for { let usr$q_i := 0 }
                                    lt(usr$q_i, 7)
                                    { usr$q_i := add(usr$q_i, 1) }
                                    {
                                        let usr$q_lhs_value := mload(add(usr$q_lhs_base, shl(5, usr$q_i)))
                                        for { let usr$q_j := 0 }
                                        lt(usr$q_j, 7)
                                        { usr$q_j := add(usr$q_j, 1) }
                                        {
                                            let usr$qconst := byte(0, mload(add(usr$q_coeff_pc, add(usr$q_i, usr$q_j))))
                                            usr$q_acc := addmod(usr$q_acc, mulmod(mulmod(usr$q_lhs_value, mload(add(usr$q_rhs_base, shl(5, usr$q_j))), usr$r), mload(add(usr$q_const_mptr, shl(5, usr$qconst))), usr$r), usr$r)
                                        }
                                    }
                                }
                                for { let usr$q_mem_block := 0 }
                                lt(usr$q_mem_block, usr$q_mem_count)
                                {
                                    usr$q_mem_block := add(usr$q_mem_block, 1)
                                }
                                {
                                    let usr$q_word := mload(usr$q_pc)
                                    let usr$qconst := byte(0, usr$q_word)
                                    let usr$q_ptr := and(shr(232, usr$q_word), 0xffff)
                                    usr$q_pc := add(usr$q_pc, 3)
                                    usr$q_acc := addmod(usr$q_acc, mulmod(mload(add(usr$q_const_mptr, shl(5, usr$qconst))), mload(usr$q_ptr), usr$r), usr$r)
                                }
                                for { let usr$q_product_block := 0 }
                                lt(usr$q_product_block, usr$q_product_count)
                                {
                                    usr$q_product_block := add(usr$q_product_block, 1)
                                }
                                {
                                    let usr$q_word := mload(usr$q_pc)
                                    let usr$qconst := byte(0, usr$q_word)
                                    let usr$q_lhs := and(shr(232, usr$q_word), 0xffff)
                                    let usr$q_rhs := and(shr(216, usr$q_word), 0xffff)
                                    usr$q_pc := add(usr$q_pc, 5)
                                    usr$q_acc := addmod(usr$q_acc, mulmod(mulmod(mload(usr$q_lhs), mload(usr$q_rhs), usr$r), mload(add(usr$q_const_mptr, shl(5, usr$qconst))), usr$r), usr$r)
                                }
                                if and(usr$q_flags, 0x01)
                                {
                                    usr$q_acc := mulmod(mload(usr$q_cond_ptr), usr$q_acc, usr$r)
                                }
                                usr$q_top := usr$q_acc
                                usr$q_has_top := 1
                            }
                            case 0x19 {
                                usr$q_top := 0
                                usr$q_has_top := 0
                                usr$q_sp := 0xa960
                                {
                                    let usr$delta := 0x8634d0aa021aaf843cab354fabb0062f6502437c6a09c006c083479590189d7
                                    let usr$q_perm_vals := 0xa960
                                    let usr$q_perm_sigmas := 0xaba0
                                    let usr$q_perm_z_cur := 0xade0
                                    let usr$q_perm_z_next := 0xaea0
                                    let usr$q_perm_z_last := 0xaf60
                                    let usr$q_perm_delta_base_ptr := 0xb000
                                    let usr$q_perm_num_cols := 18
                                    let usr$q_perm_num_sets := 6
                                    let usr$q_perm_chunk_len := 3
                                    let usr$q_perm_delta_chunk := 0x4285088329c399ea457a8ca1d30f8957e74c7f529842a1579b4fee55b3982923
                                    mstore(add(usr$q_perm_vals, 0x0), mload(0x8a20))
                                    {
                                        for {
                                            let usr$q_perm_val_load_i := 0
                                        }
                                        lt(usr$q_perm_val_load_i, 5)
                                        {
                                            usr$q_perm_val_load_i := add(usr$q_perm_val_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_val_load_dst_off := shl(5, usr$q_perm_val_load_i)
                                            let usr$q_perm_val_load_src_off := usr$q_perm_val_load_dst_off
                                            mstore(add(add(usr$q_perm_vals, 0x20), usr$q_perm_val_load_dst_off), mload(add(0x8520, usr$q_perm_val_load_src_off)))
                                        }
                                    }
                                    mstore(add(usr$q_perm_vals, 0xc0), mload(0x8500))
                                    mstore(add(usr$q_perm_vals, 0xe0), mload(28000))
                                    {
                                        for {
                                            let usr$q_perm_val_load_i := 0
                                        }
                                        lt(usr$q_perm_val_load_i, 9)
                                        {
                                            usr$q_perm_val_load_i := add(usr$q_perm_val_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_val_load_dst_off := shl(5, usr$q_perm_val_load_i)
                                            let usr$q_perm_val_load_src_off := usr$q_perm_val_load_dst_off
                                            mstore(add(add(usr$q_perm_vals, 0x100), usr$q_perm_val_load_dst_off), mload(add(0x8620, usr$q_perm_val_load_src_off)))
                                        }
                                    }
                                    mstore(add(usr$q_perm_vals, 0x220), mload(0x8a00))
                                    {
                                        for {
                                            let usr$q_perm_sigma_load_i := 0
                                        }
                                        lt(usr$q_perm_sigma_load_i, 18)
                                        {
                                            usr$q_perm_sigma_load_i := add(usr$q_perm_sigma_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_sigma_load_dst_off := shl(5, usr$q_perm_sigma_load_i)
                                            let usr$q_perm_sigma_load_src_off := usr$q_perm_sigma_load_dst_off
                                            mstore(add(add(usr$q_perm_sigmas, 0x0), usr$q_perm_sigma_load_dst_off), mload(add(0x8c40, usr$q_perm_sigma_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let usr$q_perm_z_cur_load_i := 0
                                        }
                                        lt(usr$q_perm_z_cur_load_i, 6)
                                        {
                                            usr$q_perm_z_cur_load_i := add(usr$q_perm_z_cur_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_z_cur_load_dst_off := shl(5, usr$q_perm_z_cur_load_i)
                                            let usr$q_perm_z_cur_load_src_off := mul(usr$q_perm_z_cur_load_i, 0x60)
                                            mstore(add(add(usr$q_perm_z_cur, 0x0), usr$q_perm_z_cur_load_dst_off), mload(add(0x8e80, usr$q_perm_z_cur_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let usr$q_perm_z_next_load_i := 0
                                        }
                                        lt(usr$q_perm_z_next_load_i, 6)
                                        {
                                            usr$q_perm_z_next_load_i := add(usr$q_perm_z_next_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_z_next_load_dst_off := shl(5, usr$q_perm_z_next_load_i)
                                            let usr$q_perm_z_next_load_src_off := mul(usr$q_perm_z_next_load_i, 0x60)
                                            mstore(add(add(usr$q_perm_z_next, 0x0), usr$q_perm_z_next_load_dst_off), mload(add(0x8ea0, usr$q_perm_z_next_load_src_off)))
                                        }
                                    }
                                    {
                                        for {
                                            let usr$q_perm_z_last_load_i := 0
                                        }
                                        lt(usr$q_perm_z_last_load_i, 5)
                                        {
                                            usr$q_perm_z_last_load_i := add(usr$q_perm_z_last_load_i, 1)
                                        }
                                        {
                                            let usr$q_perm_z_last_load_dst_off := shl(5, usr$q_perm_z_last_load_i)
                                            let usr$q_perm_z_last_load_src_off := mul(usr$q_perm_z_last_load_i, 0x60)
                                            mstore(add(add(usr$q_perm_z_last, 0x0), usr$q_perm_z_last_load_dst_off), mload(add(0x8ec0, usr$q_perm_z_last_load_src_off)))
                                        }
                                    }
                                    let usr$q_perm_eval := 0
                                    usr$q_perm_eval := mulmod(mload(27968), addmod(1, sub(usr$r, mload(usr$q_perm_z_cur)), usr$r), usr$r)
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    mstore(0xa300, addmod(mload(0xa300), usr$q_perm_eval, usr$r))
                                    let usr$q_perm_zn := mload(add(usr$q_perm_z_cur, 0xa0))
                                    usr$q_perm_eval := mulmod(mload(27904), addmod(mulmod(usr$q_perm_zn, usr$q_perm_zn, usr$r), sub(usr$r, usr$q_perm_zn), usr$r), usr$r)
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    mstore(0xa300, addmod(mload(0xa300), usr$q_perm_eval, usr$r))
                                    for { let usr$q_perm_i := 1 }
                                    lt(usr$q_perm_i, 6)
                                    {
                                        usr$q_perm_i := add(usr$q_perm_i, 1)
                                    }
                                    {
                                        let usr$q_perm_cur := mload(add(usr$q_perm_z_cur, shl(5, usr$q_perm_i)))
                                        let usr$q_perm_prev := mload(add(usr$q_perm_z_last, shl(5, sub(usr$q_perm_i, 1))))
                                        usr$q_perm_eval := mulmod(mload(27968), addmod(usr$q_perm_cur, sub(usr$r, usr$q_perm_prev), usr$r), usr$r)
                                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                        mstore(0xa300, addmod(mload(0xa300), usr$q_perm_eval, usr$r))
                                    }
                                    mstore(usr$q_perm_delta_base_ptr, mulmod(mload(27040), mload(27168), usr$r))
                                    for { let usr$q_perm_set := 0 }
                                    lt(usr$q_perm_set, 6)
                                    {
                                        usr$q_perm_set := add(usr$q_perm_set, 1)
                                    }
                                    {
                                        let usr$q_perm_start := mul(usr$q_perm_set, usr$q_perm_chunk_len)
                                        let usr$q_perm_end := add(usr$q_perm_start, usr$q_perm_chunk_len)
                                        if gt(usr$q_perm_end, usr$q_perm_num_cols)
                                        {
                                            usr$q_perm_end := usr$q_perm_num_cols
                                        }
                                        let usr$q_perm_left := mload(add(usr$q_perm_z_next, shl(5, usr$q_perm_set)))
                                        let usr$q_perm_right := mload(add(usr$q_perm_z_cur, shl(5, usr$q_perm_set)))
                                        let usr$q_perm_delta_pow := mload(usr$q_perm_delta_base_ptr)
                                        for {
                                            let usr$q_perm_j := usr$q_perm_start
                                        }
                                        lt(usr$q_perm_j, usr$q_perm_end)
                                        {
                                            usr$q_perm_j := add(usr$q_perm_j, 1)
                                        }
                                        {
                                            let usr$q_perm_off := shl(5, usr$q_perm_j)
                                            let usr$q_perm_v := mload(add(usr$q_perm_vals, usr$q_perm_off))
                                            let usr$q_perm_s := mload(add(usr$q_perm_sigmas, usr$q_perm_off))
                                            usr$q_perm_left := mulmod(usr$q_perm_left, addmod(addmod(usr$q_perm_v, mulmod(mload(27040), usr$q_perm_s, usr$r), usr$r), mload(27072), usr$r), usr$r)
                                            usr$q_perm_right := mulmod(usr$q_perm_right, addmod(addmod(usr$q_perm_v, usr$q_perm_delta_pow, usr$r), mload(27072), usr$r), usr$r)
                                            usr$q_perm_delta_pow := mulmod(usr$q_perm_delta_pow, usr$delta, usr$r)
                                        }
                                        usr$q_perm_eval := mulmod(addmod(1, sub(usr$r, addmod(mload(27904), mload(27936), usr$r)), usr$r), addmod(usr$q_perm_left, sub(usr$r, usr$q_perm_right), usr$r), usr$r)
                                        mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                        mstore(0xa300, addmod(mload(0xa300), usr$q_perm_eval, usr$r))
                                        mstore(usr$q_perm_delta_base_ptr, mulmod(mload(usr$q_perm_delta_base_ptr), usr$q_perm_delta_chunk, usr$r))
                                    }
                                }
                            }
                            case 0x1f {
                                usr$q_top := 0
                                usr$q_has_top := 0
                                usr$q_sp := 0xa960
                                {
                                    let usr$q_lookup_f := 0xa960
                                    let usr$q_lookup_prefix := 0xa9e0
                                    let usr$q_lookup_suffix := 0xaa60
                                    let usr$q_lookup_l0 := mload(27968)
                                    let usr$q_lookup_llast := mload(27904)
                                    let usr$q_lookup_lblind := mload(27936)
                                    let usr$q_lookup_lsum := addmod(usr$q_lookup_l0, usr$q_lookup_llast, usr$r)
                                    let usr$q_lookup_active := addmod(1, sub(usr$r, addmod(usr$q_lookup_llast, usr$q_lookup_lblind, usr$r)), usr$r)
                                    let usr$q_lookup_beta := mload(27040)
                                    let usr$q_lookup_theta := mload(27008)
                                    {
                                        {
                                            let usr$q_lookup_eval := mulmod(usr$q_lookup_lsum, mload(0x90e0), usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                        {
                                            let usr$f_10 := mload(0x8b60)
                                            let usr$var0 := addmod(mulmod(0, usr$q_lookup_theta, usr$r), usr$f_10, usr$r)
                                            let usr$var1 := mulmod(usr$var0, usr$q_lookup_theta, usr$r)
                                            for {
                                                let usr$q_lookup_shared_i := 0
                                            }
                                            lt(usr$q_lookup_shared_i, 4)
                                            {
                                                usr$q_lookup_shared_i := add(usr$q_lookup_shared_i, 1)
                                            }
                                            {
                                                let usr$q_lookup_shared_off := shl(5, usr$q_lookup_shared_i)
                                                let usr$q_lookup_shared_tail := mload(add(0x8540, usr$q_lookup_shared_off))
                                                let usr$q_lookup_shared_compressed := addmod(usr$var1, usr$q_lookup_shared_tail, usr$r)
                                                mstore(add(usr$q_lookup_f, usr$q_lookup_shared_off), addmod(usr$q_lookup_shared_compressed, usr$q_lookup_beta, usr$r))
                                            }
                                            let usr$q_lookup_product := 1
                                            for { let usr$q_lookup_prod_i := 0 }
                                            lt(usr$q_lookup_prod_i, 4)
                                            {
                                                usr$q_lookup_prod_i := add(usr$q_lookup_prod_i, 1)
                                            }
                                            {
                                                usr$q_lookup_product := mulmod(usr$q_lookup_product, mload(add(usr$q_lookup_f, shl(5, usr$q_lookup_prod_i))), usr$r)
                                            }
                                            mstore(usr$q_lookup_prefix, 1)
                                            for { let usr$q_lookup_pref_i := 1 }
                                            lt(usr$q_lookup_pref_i, 4)
                                            {
                                                usr$q_lookup_pref_i := add(usr$q_lookup_pref_i, 1)
                                            }
                                            {
                                                let usr$q_lookup_pref_prev := sub(usr$q_lookup_pref_i, 1)
                                                mstore(add(usr$q_lookup_prefix, shl(5, usr$q_lookup_pref_i)), mulmod(mload(add(usr$q_lookup_prefix, shl(5, usr$q_lookup_pref_prev))), mload(add(usr$q_lookup_f, shl(5, usr$q_lookup_pref_prev))), usr$r))
                                            }
                                            mstore(add(usr$q_lookup_suffix, 0x60), 1)
                                            for {
                                                let usr$q_lookup_suf_i := sub(4, 1)
                                            }
                                            gt(usr$q_lookup_suf_i, 0)
                                            {
                                                usr$q_lookup_suf_i := sub(usr$q_lookup_suf_i, 1)
                                            }
                                            {
                                                let usr$q_lookup_suf_prev := sub(usr$q_lookup_suf_i, 1)
                                                mstore(add(usr$q_lookup_suffix, shl(5, usr$q_lookup_suf_prev)), mulmod(mload(add(usr$q_lookup_suffix, shl(5, usr$q_lookup_suf_i))), mload(add(usr$q_lookup_f, shl(5, usr$q_lookup_suf_i))), usr$r))
                                            }
                                            let usr$q_lookup_sum := 0
                                            for { let usr$q_lookup_sum_i := 0 }
                                            lt(usr$q_lookup_sum_i, 4)
                                            {
                                                usr$q_lookup_sum_i := add(usr$q_lookup_sum_i, 1)
                                            }
                                            {
                                                usr$q_lookup_sum := addmod(usr$q_lookup_sum, mulmod(mload(add(usr$q_lookup_prefix, shl(5, usr$q_lookup_sum_i))), mload(add(usr$q_lookup_suffix, shl(5, usr$q_lookup_sum_i))), usr$r), usr$r)
                                            }
                                            let usr$q_lookup_eval := addmod(mulmod(mload(0x90c0), usr$q_lookup_product, usr$r), sub(usr$r, usr$q_lookup_sum), usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                        {
                                            let usr$q_lookup_sum_h := mload(0x90c0)
                                            let usr$f_17 := mload(0x8be0)
                                            let usr$f_11 := mload(0x8b80)
                                            let usr$var0 := addmod(mulmod(0, usr$q_lookup_theta, usr$r), usr$f_11, usr$r)
                                            let usr$f_12 := mload(0x8ba0)
                                            let usr$var1 := addmod(mulmod(usr$var0, usr$q_lookup_theta, usr$r), usr$f_12, usr$r)
                                            let usr$q_lookup_s_sum_h := mulmod(usr$f_17, usr$q_lookup_sum_h, usr$r)
                                            let usr$q_lookup_diff := addmod(mload(0x9100), sub(usr$r, addmod(mload(0x90e0), usr$q_lookup_s_sum_h, usr$r)), usr$r)
                                            let usr$q_lookup_t_beta := addmod(usr$var1, usr$q_lookup_beta, usr$r)
                                            let usr$q_lookup_core := addmod(mulmod(usr$q_lookup_diff, usr$q_lookup_t_beta, usr$r), mload(0x90a0), usr$r)
                                            let usr$q_lookup_eval := mulmod(usr$q_lookup_active, usr$q_lookup_core, usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                    }
                                    {
                                        {
                                            let usr$q_lookup_eval := mulmod(usr$q_lookup_lsum, mload(0x9160), usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                        {
                                            let usr$a_14 := mload(0x8a00)
                                            let usr$var0 := addmod(mulmod(0, usr$q_lookup_theta, usr$r), usr$a_14, usr$r)
                                            let usr$a_0 := mload(0x8520)
                                            let usr$var1 := addmod(mulmod(usr$var0, usr$q_lookup_theta, usr$r), usr$a_0, usr$r)
                                            let usr$a_1 := mload(0x8540)
                                            let usr$var2 := addmod(mulmod(usr$var1, usr$q_lookup_theta, usr$r), usr$a_1, usr$r)
                                            let usr$a_2 := mload(0x8560)
                                            let usr$var3 := addmod(mulmod(usr$var2, usr$q_lookup_theta, usr$r), usr$a_2, usr$r)
                                            let usr$a_3 := mload(0x8580)
                                            let usr$var4 := addmod(mulmod(usr$var3, usr$q_lookup_theta, usr$r), usr$a_3, usr$r)
                                            let usr$a_4 := mload(0x85a0)
                                            let usr$var5 := addmod(mulmod(usr$var4, usr$q_lookup_theta, usr$r), usr$a_4, usr$r)
                                            let usr$a_5 := mload(0x8620)
                                            let usr$var6 := addmod(mulmod(usr$var5, usr$q_lookup_theta, usr$r), usr$a_5, usr$r)
                                            let usr$a_6 := mload(0x8640)
                                            let usr$var7 := addmod(mulmod(usr$var6, usr$q_lookup_theta, usr$r), usr$a_6, usr$r)
                                            let usr$a_7 := mload(0x8660)
                                            let usr$var8 := addmod(mulmod(usr$var7, usr$q_lookup_theta, usr$r), usr$a_7, usr$r)
                                            let usr$a_8 := mload(0x8680)
                                            let usr$var9 := addmod(mulmod(usr$var8, usr$q_lookup_theta, usr$r), usr$a_8, usr$r)
                                            let usr$a_9 := mload(0x86a0)
                                            let usr$var10 := addmod(mulmod(usr$var9, usr$q_lookup_theta, usr$r), usr$a_9, usr$r)
                                            let usr$a_10 := mload(0x86c0)
                                            let usr$var11 := addmod(mulmod(usr$var10, usr$q_lookup_theta, usr$r), usr$a_10, usr$r)
                                            let usr$a_11 := mload(0x86e0)
                                            let usr$var12 := addmod(mulmod(usr$var11, usr$q_lookup_theta, usr$r), usr$a_11, usr$r)
                                            let usr$a_12 := mload(0x8700)
                                            let usr$var13 := addmod(mulmod(usr$var12, usr$q_lookup_theta, usr$r), usr$a_12, usr$r)
                                            let usr$a_13 := mload(0x8720)
                                            let usr$var14 := addmod(mulmod(usr$var13, usr$q_lookup_theta, usr$r), usr$a_13, usr$r)
                                            let usr$f_13 := mload(0x8bc0)
                                            let usr$var15 := addmod(mulmod(usr$var14, usr$q_lookup_theta, usr$r), usr$f_13, usr$r)
                                            let usr$q_lookup_eval := addmod(mulmod(mload(0x9140), addmod(usr$var15, usr$q_lookup_beta, usr$r), usr$r), sub(usr$r, 1), usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                        {
                                            let usr$q_lookup_sum_h := mload(0x9140)
                                            let usr$var0 := 0x1
                                            let usr$f_24 := mload(0x8c00)
                                            let usr$var1 := addmod(0, sub(usr$r, usr$f_24), usr$r)
                                            let usr$var2 := addmod(usr$var0, usr$var1, usr$r)
                                            let usr$a_14 := mload(0x8a00)
                                            let usr$var3 := mulmod(usr$var2, usr$a_14, usr$r)
                                            let usr$var4 := addmod(mulmod(0, usr$q_lookup_theta, usr$r), usr$var3, usr$r)
                                            let usr$a_0 := mload(0x8520)
                                            let usr$var5 := mulmod(usr$var2, usr$a_0, usr$r)
                                            let usr$var6 := addmod(mulmod(usr$var4, usr$q_lookup_theta, usr$r), usr$var5, usr$r)
                                            let usr$a_1 := mload(0x8540)
                                            let usr$var7 := mulmod(usr$var2, usr$a_1, usr$r)
                                            let usr$var8 := addmod(mulmod(usr$var6, usr$q_lookup_theta, usr$r), usr$var7, usr$r)
                                            let usr$a_2 := mload(0x8560)
                                            let usr$var9 := mulmod(usr$var2, usr$a_2, usr$r)
                                            let usr$var10 := addmod(mulmod(usr$var8, usr$q_lookup_theta, usr$r), usr$var9, usr$r)
                                            let usr$a_3 := mload(0x8580)
                                            let usr$var11 := mulmod(usr$var2, usr$a_3, usr$r)
                                            let usr$var12 := addmod(mulmod(usr$var10, usr$q_lookup_theta, usr$r), usr$var11, usr$r)
                                            let usr$a_4 := mload(0x85a0)
                                            let usr$var13 := mulmod(usr$var2, usr$a_4, usr$r)
                                            let usr$var14 := addmod(mulmod(usr$var12, usr$q_lookup_theta, usr$r), usr$var13, usr$r)
                                            let usr$a_5 := mload(0x8620)
                                            let usr$var15 := mulmod(usr$var2, usr$a_5, usr$r)
                                            let usr$var16 := addmod(mulmod(usr$var14, usr$q_lookup_theta, usr$r), usr$var15, usr$r)
                                            let usr$a_6 := mload(0x8640)
                                            let usr$var17 := mulmod(usr$var2, usr$a_6, usr$r)
                                            let usr$var18 := addmod(mulmod(usr$var16, usr$q_lookup_theta, usr$r), usr$var17, usr$r)
                                            let usr$a_7 := mload(0x8660)
                                            let usr$var19 := mulmod(usr$var2, usr$a_7, usr$r)
                                            let usr$var20 := addmod(mulmod(usr$var18, usr$q_lookup_theta, usr$r), usr$var19, usr$r)
                                            let usr$a_8 := mload(0x8680)
                                            let usr$var21 := mulmod(usr$var2, usr$a_8, usr$r)
                                            let usr$var22 := addmod(mulmod(usr$var20, usr$q_lookup_theta, usr$r), usr$var21, usr$r)
                                            let usr$a_9 := mload(0x86a0)
                                            let usr$var23 := mulmod(usr$var2, usr$a_9, usr$r)
                                            let usr$var24 := addmod(mulmod(usr$var22, usr$q_lookup_theta, usr$r), usr$var23, usr$r)
                                            let usr$a_10 := mload(0x86c0)
                                            let usr$var25 := mulmod(usr$var2, usr$a_10, usr$r)
                                            let usr$var26 := addmod(mulmod(usr$var24, usr$q_lookup_theta, usr$r), usr$var25, usr$r)
                                            let usr$a_11 := mload(0x86e0)
                                            let usr$var27 := mulmod(usr$var2, usr$a_11, usr$r)
                                            let usr$var28 := addmod(mulmod(usr$var26, usr$q_lookup_theta, usr$r), usr$var27, usr$r)
                                            let usr$a_12 := mload(0x8700)
                                            let usr$var29 := mulmod(usr$var2, usr$a_12, usr$r)
                                            let usr$var30 := addmod(mulmod(usr$var28, usr$q_lookup_theta, usr$r), usr$var29, usr$r)
                                            let usr$a_13 := mload(0x8720)
                                            let usr$var31 := mulmod(usr$var2, usr$a_13, usr$r)
                                            let usr$var32 := addmod(mulmod(usr$var30, usr$q_lookup_theta, usr$r), usr$var31, usr$r)
                                            let usr$f_13 := mload(0x8bc0)
                                            let usr$var33 := mulmod(usr$var2, usr$f_13, usr$r)
                                            let usr$var34 := addmod(mulmod(usr$var32, usr$q_lookup_theta, usr$r), usr$var33, usr$r)
                                            let usr$q_lookup_s_sum_h := mulmod(usr$var0, usr$q_lookup_sum_h, usr$r)
                                            let usr$q_lookup_diff := addmod(mload(0x9180), sub(usr$r, addmod(mload(0x9160), usr$q_lookup_s_sum_h, usr$r)), usr$r)
                                            let usr$q_lookup_t_beta := addmod(usr$var34, usr$q_lookup_beta, usr$r)
                                            let usr$q_lookup_core := addmod(mulmod(usr$q_lookup_diff, usr$q_lookup_t_beta, usr$r), mload(0x9120), usr$r)
                                            let usr$q_lookup_eval := mulmod(usr$q_lookup_active, usr$q_lookup_core, usr$r)
                                            mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                            mstore(0xa300, addmod(mload(0xa300), usr$q_lookup_eval, usr$r))
                                        }
                                    }
                                }
                            }
                            case 0x1b {
                                let usr$q_native_idx := shr(240, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 2)
                                usr$q_top := 0
                                usr$q_has_top := 0
                                usr$q_sp := 0xa960
                                switch usr$q_native_idx
                                case 0 {
                                    {
                                        let usr$var0 := 0x1
                                        let usr$a_0 := mload(0x8520)
                                        let usr$a_0_next_1 := mload(0x85c0)
                                        let usr$var1 := mulmod(usr$a_0, usr$a_0_next_1, usr$r)
                                        let usr$var2 := 0x100000000000000
                                        let usr$a_1_next_1 := mload(0x85e0)
                                        let usr$var3 := mulmod(usr$a_0, usr$a_1_next_1, usr$r)
                                        let usr$var4 := mulmod(usr$var2, usr$var3, usr$r)
                                        let usr$var5 := addmod(usr$var1, usr$var4, usr$r)
                                        let usr$var6 := 0x10000000000000000000000000000
                                        let usr$a_2_next_1 := mload(0x8600)
                                        let usr$var7 := mulmod(usr$a_0, usr$a_2_next_1, usr$r)
                                        let usr$var8 := mulmod(usr$var6, usr$var7, usr$r)
                                        let usr$var9 := addmod(usr$var5, usr$var8, usr$r)
                                        let usr$a_1 := mload(0x8540)
                                        let usr$var10 := mulmod(usr$a_1, usr$a_0_next_1, usr$r)
                                        let usr$var11 := mulmod(usr$var2, usr$var10, usr$r)
                                        let usr$var12 := addmod(usr$var9, usr$var11, usr$r)
                                        let usr$var13 := mulmod(usr$a_1, usr$a_1_next_1, usr$r)
                                        let usr$var14 := mulmod(usr$var6, usr$var13, usr$r)
                                        let usr$var15 := addmod(usr$var12, usr$var14, usr$r)
                                        let usr$var16 := 0x3212e00cde6d2002b119d800000347fcb8
                                        let usr$a_6_next_1 := mload(0x87a0)
                                        let usr$var17 := mulmod(usr$a_1, usr$a_6_next_1, usr$r)
                                        let usr$var18 := mulmod(usr$var16, usr$var17, usr$r)
                                        let usr$var19 := addmod(usr$var15, usr$var18, usr$r)
                                        let usr$a_2 := mload(0x8560)
                                        let usr$var20 := mulmod(usr$a_2, usr$a_0_next_1, usr$r)
                                        let usr$var21 := mulmod(usr$var6, usr$var20, usr$r)
                                        let usr$var22 := addmod(usr$var19, usr$var21, usr$r)
                                        let usr$a_5_next_1 := mload(0x8780)
                                        let usr$var23 := mulmod(usr$a_2, usr$a_5_next_1, usr$r)
                                        let usr$var24 := mulmod(usr$var16, usr$var23, usr$r)
                                        let usr$var25 := addmod(usr$var22, usr$var24, usr$r)
                                        let usr$var26 := 0x297784894e27525bc342b7fde37dba9366
                                        let usr$var27 := mulmod(usr$a_2, usr$a_6_next_1, usr$r)
                                        let usr$var28 := mulmod(usr$var26, usr$var27, usr$r)
                                        let usr$var29 := addmod(usr$var25, usr$var28, usr$r)
                                        let usr$a_3 := mload(0x8580)
                                        let usr$a_4_next_1 := mload(0x8760)
                                        let usr$var30 := mulmod(usr$a_3, usr$a_4_next_1, usr$r)
                                        let usr$var31 := mulmod(usr$var16, usr$var30, usr$r)
                                        let usr$var32 := addmod(usr$var29, usr$var31, usr$r)
                                        let usr$var33 := mulmod(usr$a_3, usr$a_5_next_1, usr$r)
                                        let usr$var34 := mulmod(usr$var26, usr$var33, usr$r)
                                        let usr$var35 := addmod(usr$var32, usr$var34, usr$r)
                                        let usr$var36 := 0x340f2ebe380a0f5eff4360543988a61dc2
                                        let usr$var37 := mulmod(usr$a_3, usr$a_6_next_1, usr$r)
                                        let usr$var38 := mulmod(usr$var36, usr$var37, usr$r)
                                        let usr$var39 := addmod(usr$var35, usr$var38, usr$r)
                                        let usr$a_4 := mload(0x85a0)
                                        let usr$a_3_next_1 := mload(0x8740)
                                        let usr$var40 := mulmod(usr$a_4, usr$a_3_next_1, usr$r)
                                        let usr$var41 := mulmod(usr$var16, usr$var40, usr$r)
                                        let usr$var42 := addmod(usr$var39, usr$var41, usr$r)
                                        let usr$var43 := mulmod(usr$a_4, usr$a_4_next_1, usr$r)
                                        let usr$var44 := mulmod(usr$var26, usr$var43, usr$r)
                                        let usr$var45 := addmod(usr$var42, usr$var44, usr$r)
                                        let usr$var46 := mulmod(usr$a_4, usr$a_5_next_1, usr$r)
                                        let usr$var47 := mulmod(usr$var36, usr$var46, usr$r)
                                        let usr$var48 := addmod(usr$var45, usr$var47, usr$r)
                                        let usr$var49 := 0x13af65741744bd7bb2c6872df2b800320
                                        let usr$var50 := mulmod(usr$a_4, usr$a_6_next_1, usr$r)
                                        let usr$var51 := mulmod(usr$var49, usr$var50, usr$r)
                                        let usr$var52 := addmod(usr$var48, usr$var51, usr$r)
                                        let usr$a_5 := mload(0x8620)
                                        let usr$var53 := mulmod(usr$a_5, usr$a_2_next_1, usr$r)
                                        let usr$var54 := mulmod(usr$var16, usr$var53, usr$r)
                                        let usr$var55 := addmod(usr$var52, usr$var54, usr$r)
                                        let usr$var56 := mulmod(usr$a_5, usr$a_3_next_1, usr$r)
                                        let usr$var57 := mulmod(usr$var26, usr$var56, usr$r)
                                        let usr$var58 := addmod(usr$var55, usr$var57, usr$r)
                                        let usr$var59 := mulmod(usr$a_5, usr$a_4_next_1, usr$r)
                                        let usr$var60 := mulmod(usr$var36, usr$var59, usr$r)
                                        let usr$var61 := addmod(usr$var58, usr$var60, usr$r)
                                        let usr$var62 := mulmod(usr$a_5, usr$a_5_next_1, usr$r)
                                        let usr$var63 := mulmod(usr$var49, usr$var62, usr$r)
                                        let usr$var64 := addmod(usr$var61, usr$var63, usr$r)
                                        let usr$var65 := 0x2cb9b546d20373eaf85e8f53db883cb548
                                        let usr$var66 := mulmod(usr$a_5, usr$a_6_next_1, usr$r)
                                        let usr$var67 := mulmod(usr$var65, usr$var66, usr$r)
                                        let usr$var68 := addmod(usr$var64, usr$var67, usr$r)
                                        let usr$a_6 := mload(0x8640)
                                        let usr$var69 := mulmod(usr$a_6, usr$a_1_next_1, usr$r)
                                        let usr$var70 := mulmod(usr$var16, usr$var69, usr$r)
                                        let usr$var71 := addmod(usr$var68, usr$var70, usr$r)
                                        let usr$var72 := mulmod(usr$a_6, usr$a_2_next_1, usr$r)
                                        let usr$var73 := mulmod(usr$var26, usr$var72, usr$r)
                                        let usr$var74 := addmod(usr$var71, usr$var73, usr$r)
                                        let usr$var75 := mulmod(usr$a_6, usr$a_3_next_1, usr$r)
                                        let usr$var76 := mulmod(usr$var36, usr$var75, usr$r)
                                        let usr$var77 := addmod(usr$var74, usr$var76, usr$r)
                                        let usr$var78 := mulmod(usr$a_6, usr$a_4_next_1, usr$r)
                                        let usr$var79 := mulmod(usr$var49, usr$var78, usr$r)
                                        let usr$var80 := addmod(usr$var77, usr$var79, usr$r)
                                        let usr$var81 := mulmod(usr$a_6, usr$a_5_next_1, usr$r)
                                        let usr$var82 := mulmod(usr$var65, usr$var81, usr$r)
                                        let usr$var83 := addmod(usr$var80, usr$var82, usr$r)
                                        let usr$var84 := 0xc8557e86f90d0d89eed6eb5349a0f8820
                                        let usr$var85 := mulmod(usr$a_6, usr$a_6_next_1, usr$r)
                                        let usr$var86 := mulmod(usr$var84, usr$var85, usr$r)
                                        let usr$var87 := addmod(usr$var83, usr$var86, usr$r)
                                        let usr$var88 := mulmod(usr$var2, usr$a_1, usr$r)
                                        let usr$var89 := addmod(usr$a_0, usr$var88, usr$r)
                                        let usr$var90 := mulmod(usr$var6, usr$a_2, usr$r)
                                        let usr$var91 := addmod(usr$var89, usr$var90, usr$r)
                                        let usr$var92 := addmod(usr$var87, usr$var91, usr$r)
                                        let usr$var93 := mulmod(usr$var2, usr$a_1_next_1, usr$r)
                                        let usr$var94 := addmod(usr$a_0_next_1, usr$var93, usr$r)
                                        let usr$var95 := mulmod(usr$var6, usr$a_2_next_1, usr$r)
                                        let usr$var96 := addmod(usr$var94, usr$var95, usr$r)
                                        let usr$var97 := addmod(usr$var92, usr$var96, usr$r)
                                        let usr$a_7 := mload(0x8660)
                                        let usr$a_8 := mload(0x8680)
                                        let usr$var98 := mulmod(usr$var2, usr$a_8, usr$r)
                                        let usr$var99 := addmod(usr$a_7, usr$var98, usr$r)
                                        let usr$a_9 := mload(0x86a0)
                                        let usr$var100 := mulmod(usr$var6, usr$a_9, usr$r)
                                        let usr$var101 := addmod(usr$var99, usr$var100, usr$r)
                                        let usr$var102 := addmod(0, sub(usr$r, usr$var101), usr$r)
                                        let usr$var103 := addmod(usr$var97, usr$var102, usr$r)
                                        let usr$a_7_next_1 := mload(0x87c0)
                                        let usr$var104 := 0x241eabfffeb153ffffb9feffffffffaaab
                                        let usr$var105 := mulmod(usr$a_7_next_1, usr$var104, usr$r)
                                        let usr$var106 := addmod(0, sub(usr$r, usr$var105), usr$r)
                                        let usr$var107 := addmod(usr$var103, usr$var106, usr$r)
                                        let usr$var108 := addmod(0, sub(usr$r, usr$var16), usr$r)
                                        let usr$var109 := addmod(usr$var107, usr$var108, usr$r)
                                        let usr$a_8_next_1 := mload(0x87e0)
                                        let usr$var110 := 0x73eda753299d7d483339d80809a1d80553b9202d7ffe85d4800008bb20000001
                                        let usr$var111 := addmod(usr$a_8_next_1, usr$var110, usr$r)
                                        let usr$var112 := 0x4000000000000000000000000000000000
                                        let usr$var113 := mulmod(usr$var111, usr$var112, usr$r)
                                        let usr$var114 := addmod(0, sub(usr$r, usr$var113), usr$r)
                                        let usr$var115 := addmod(usr$var109, usr$var114, usr$r)
                                        let usr$var116 := mulmod(usr$var0, usr$var115, usr$r)
                                        mstore(0xa960, usr$var116)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    {
                                        let usr$q_selector_ptr := add(41408, 0x60)
                                        let usr$q_selector_acc := mload(usr$q_selector_ptr)
                                        mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                                    }
                                }
                                case 1 {
                                    {
                                        let usr$var0 := 0x1
                                        let usr$a_0 := mload(0x8520)
                                        let usr$var1 := 0x10000000000000000000000000000
                                        let usr$var2 := addmod(usr$a_0, usr$var1, usr$r)
                                        let usr$var3 := 0x100000000000000
                                        let usr$a_1 := mload(0x8540)
                                        let usr$var4 := addmod(usr$a_1, usr$var1, usr$r)
                                        let usr$var5 := mulmod(usr$var3, usr$var4, usr$r)
                                        let usr$var6 := addmod(usr$var2, usr$var5, usr$r)
                                        let usr$a_2 := mload(0x8560)
                                        let usr$var7 := addmod(usr$a_2, usr$var1, usr$r)
                                        let usr$var8 := mulmod(usr$var1, usr$var7, usr$r)
                                        let usr$var9 := addmod(usr$var6, usr$var8, usr$r)
                                        let usr$a_7 := mload(0x8660)
                                        let usr$a_8 := mload(0x8680)
                                        let usr$var10 := mulmod(usr$var3, usr$a_8, usr$r)
                                        let usr$var11 := addmod(usr$a_7, usr$var10, usr$r)
                                        let usr$a_9 := mload(0x86a0)
                                        let usr$var12 := mulmod(usr$var1, usr$a_9, usr$r)
                                        let usr$var13 := addmod(usr$var11, usr$var12, usr$r)
                                        let usr$var14 := addmod(0, sub(usr$r, usr$var13), usr$r)
                                        let usr$var15 := addmod(usr$var9, usr$var14, usr$r)
                                        let usr$var16 := addmod(0, sub(usr$r, usr$var1), usr$r)
                                        let usr$var17 := addmod(usr$var15, usr$var16, usr$r)
                                        let usr$a_7_next_1 := mload(0x87c0)
                                        let usr$var18 := 0x241eabfffeb153ffffb9feffffffffaaab
                                        let usr$var19 := mulmod(usr$a_7_next_1, usr$var18, usr$r)
                                        let usr$var20 := addmod(0, sub(usr$r, usr$var19), usr$r)
                                        let usr$var21 := addmod(usr$var17, usr$var20, usr$r)
                                        let usr$var22 := 0xd9d44a30b019261257667fde3844a8cd6
                                        let usr$var23 := addmod(0, sub(usr$r, usr$var22), usr$r)
                                        let usr$var24 := addmod(usr$var21, usr$var23, usr$r)
                                        let usr$a_8_next_1 := mload(0x87e0)
                                        let usr$var25 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5b6e855000003ab00002
                                        let usr$var26 := addmod(usr$a_8_next_1, usr$var25, usr$r)
                                        let usr$var27 := 0x4000000000000000000000000000000000
                                        let usr$var28 := mulmod(usr$var26, usr$var27, usr$r)
                                        let usr$var29 := addmod(0, sub(usr$r, usr$var28), usr$r)
                                        let usr$var30 := addmod(usr$var24, usr$var29, usr$r)
                                        let usr$var31 := mulmod(usr$var0, usr$var30, usr$r)
                                        mstore(0xa960, usr$var31)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    {
                                        let usr$q_selector_ptr := add(41408, 0x80)
                                        let usr$q_selector_acc := mload(usr$q_selector_ptr)
                                        mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                                    }
                                }
                                case 2 {
                                    {
                                        let usr$var0 := 0x1
                                        let usr$f_0 := mload(0x8ae0)
                                        let usr$a_0_next_1 := mload(0x85c0)
                                        let usr$var1 := addmod(0, sub(usr$r, usr$a_0_next_1), usr$r)
                                        let usr$var2 := addmod(usr$f_0, usr$var1, usr$r)
                                        let usr$var3 := 0x1b8114c381b922fd5d6d241210e2d8a68ad5744053ba9e776118de4107b51ace
                                        let usr$a_0 := mload(0x8520)
                                        let usr$var4 := mulmod(usr$a_0, usr$a_0, usr$r)
                                        let usr$a_3 := mload(0x8580)
                                        let usr$var5 := mulmod(usr$var4, usr$a_3, usr$r)
                                        let usr$var6 := mulmod(usr$var3, usr$var5, usr$r)
                                        let usr$var7 := addmod(usr$var2, usr$var6, usr$r)
                                        let usr$var8 := 0x3df32e4cc4cb2ed20e5d21899cf5331775990ccaec4c09b4e3717213fcc0d763
                                        let usr$a_1 := mload(0x8540)
                                        let usr$var9 := mulmod(usr$a_1, usr$a_1, usr$r)
                                        let usr$a_4 := mload(0x85a0)
                                        let usr$var10 := mulmod(usr$var9, usr$a_4, usr$r)
                                        let usr$var11 := mulmod(usr$var8, usr$var10, usr$r)
                                        let usr$var12 := addmod(usr$var7, usr$var11, usr$r)
                                        let usr$var13 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                                        let usr$a_2 := mload(0x8560)
                                        let usr$var14 := mulmod(usr$a_2, usr$a_2, usr$r)
                                        let usr$a_5 := mload(0x8620)
                                        let usr$var15 := mulmod(usr$var14, usr$a_5, usr$r)
                                        let usr$var16 := mulmod(usr$var13, usr$var15, usr$r)
                                        let usr$var17 := addmod(usr$var12, usr$var16, usr$r)
                                        let usr$var18 := mulmod(usr$var0, usr$var17, usr$r)
                                        mstore(0xa960, usr$var18)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    {
                                        let usr$q_selector_ptr := add(41408, 0x120)
                                        let usr$q_selector_acc := mload(usr$q_selector_ptr)
                                        usr$q_selector_acc := mulmod(usr$q_selector_acc, mload(add(0xa340, 0x20)), usr$r)
                                        mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                                    }
                                }
                                case 3 {
                                    {
                                        let usr$var0 := 0x1
                                        let usr$f_1 := mload(0x8b00)
                                        let usr$a_1_next_1 := mload(0x85e0)
                                        let usr$var1 := addmod(0, sub(usr$r, usr$a_1_next_1), usr$r)
                                        let usr$var2 := addmod(usr$f_1, usr$var1, usr$r)
                                        let usr$var3 := 0x404d21073985d14e432a4ad76d3fae06ca74314b950fe7b1d7f501cd31a8b374
                                        let usr$a_0 := mload(0x8520)
                                        let usr$var4 := mulmod(usr$a_0, usr$a_0, usr$r)
                                        let usr$a_3 := mload(0x8580)
                                        let usr$var5 := mulmod(usr$var4, usr$a_3, usr$r)
                                        let usr$var6 := mulmod(usr$var3, usr$var5, usr$r)
                                        let usr$var7 := addmod(usr$var2, usr$var6, usr$r)
                                        let usr$var8 := 0xb2cc8704264c6bd81bc620e9e524d4b73e9b2317679422ff7fa1603955649f1
                                        let usr$a_1 := mload(0x8540)
                                        let usr$var9 := mulmod(usr$a_1, usr$a_1, usr$r)
                                        let usr$a_4 := mload(0x85a0)
                                        let usr$var10 := mulmod(usr$var9, usr$a_4, usr$r)
                                        let usr$var11 := mulmod(usr$var8, usr$var10, usr$r)
                                        let usr$var12 := addmod(usr$var7, usr$var11, usr$r)
                                        let usr$var13 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                                        let usr$a_2 := mload(0x8560)
                                        let usr$var14 := mulmod(usr$a_2, usr$a_2, usr$r)
                                        let usr$a_5 := mload(0x8620)
                                        let usr$var15 := mulmod(usr$var14, usr$a_5, usr$r)
                                        let usr$var16 := mulmod(usr$var13, usr$var15, usr$r)
                                        let usr$var17 := addmod(usr$var12, usr$var16, usr$r)
                                        let usr$var18 := mulmod(usr$var0, usr$var17, usr$r)
                                        mstore(0xa960, usr$var18)
                                    }
                                    mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                    {
                                        let usr$q_selector_ptr := add(41408, 0x120)
                                        let usr$q_selector_acc := mload(usr$q_selector_ptr)
                                        usr$q_selector_acc := mulmod(usr$q_selector_acc, mload(add(0xa340, 0x20)), usr$r)
                                        mstore(usr$q_selector_ptr, addmod(usr$q_selector_acc, mload(0xa960), usr$r))
                                    }
                                }
                                default { revert(0, 0) }
                            }
                            case 0x0b {
                                let usr$q_selector_payload := shr(232, mload(usr$q_pc))
                                usr$q_pc := add(usr$q_pc, 3)
                                let usr$q_sel_idx := shr(16, usr$q_selector_payload)
                                let usr$q_sel_gap := and(usr$q_selector_payload, 0xffff)
                                let usr$q_eval := usr$q_top
                                usr$q_has_top := 0
                                mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                let usr$q_target_ptr := add(41408, shl(5, usr$q_sel_idx))
                                let usr$q_sel_acc := mload(usr$q_target_ptr)
                                if usr$q_sel_gap
                                {
                                    usr$q_sel_acc := mulmod(usr$q_sel_acc, mload(add(0xa340, shl(5, usr$q_sel_gap))), usr$r)
                                }
                                mstore(usr$q_target_ptr, addmod(usr$q_sel_acc, usr$q_eval, usr$r))
                            }
                            default { revert(0, 0) }
                        }
                        if iszero(eq(usr$q_pc, usr$q_end)) { revert(0, 0) }
                        if usr$q_has_top { revert(0, 0) }
                        {
                            let usr$q_trash_tau := mload(27104)
                            {
                                let usr$f_0 := mload(0x8ae0)
                                let usr$a_0_next_1 := mload(0x85c0)
                                let usr$var0 := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000000
                                let usr$var1 := mulmod(usr$a_0_next_1, usr$var0, usr$r)
                                let usr$var2 := addmod(usr$f_0, usr$var1, usr$r)
                                let usr$var3 := 0x590ba402032e82eb1f660ef09796c5686345a5054ed96dae8e2d233633788771
                                let usr$a_0 := mload(0x8520)
                                let usr$var4 := mulmod(usr$var3, usr$a_0, usr$r)
                                let usr$var5 := addmod(usr$var2, usr$var4, usr$r)
                                let usr$var6 := 0x52f789e4afc3801f7411102ee2f47cc5954a744e71cac98e75ea962a55a0a76f
                                let usr$a_1 := mload(0x8540)
                                let usr$var7 := mulmod(usr$var6, usr$a_1, usr$r)
                                let usr$var8 := addmod(usr$var5, usr$var7, usr$r)
                                let usr$var9 := 0x3509dd2fe3aac0080783557fec090fb1cb4b2b0901253c55282024331d1fe1a8
                                let usr$a_2 := mload(0x8560)
                                let usr$var10 := usr$q_pow5(usr$a_2)
                                let usr$var11 := mulmod(usr$var9, usr$var10, usr$r)
                                let usr$var12 := addmod(usr$var8, usr$var11, usr$r)
                                let usr$var13 := 0x333f8046ece5579cbd6872449c57f2703dfc8864cfadc06d587ff104a0d0c1f2
                                let usr$a_3 := mload(0x8580)
                                let usr$var14 := usr$q_pow5(usr$a_3)
                                let usr$var15 := mulmod(usr$var13, usr$var14, usr$r)
                                let usr$var16 := addmod(usr$var12, usr$var15, usr$r)
                                let usr$var17 := 0x412c98232b6ab8a47aa76ee814ef7ec6261987c9802f2cfc490e007951a60ca5
                                let usr$a_4 := mload(0x85a0)
                                let usr$var18 := usr$q_pow5(usr$a_4)
                                let usr$var19 := mulmod(usr$var17, usr$var18, usr$r)
                                let usr$var20 := addmod(usr$var16, usr$var19, usr$r)
                                let usr$var21 := 0x53fded36d490ba6b05a5d10fd99ffe5456baec6a6a8753199d5ebdc33c99790e
                                let usr$a_5 := mload(0x8620)
                                let usr$var22 := usr$q_pow5(usr$a_5)
                                let usr$var23 := mulmod(usr$var21, usr$var22, usr$r)
                                let usr$var24 := addmod(usr$var20, usr$var23, usr$r)
                                let usr$var25 := 0x6ccb1c7d87f3c12a2bde4e68ac7f1e8b03481ba15d7f88f9a7f9b8310dd6d34
                                let usr$a_6 := mload(0x8640)
                                let usr$var26 := usr$q_pow5(usr$a_6)
                                let usr$var27 := mulmod(usr$var25, usr$var26, usr$r)
                                let usr$var28 := addmod(usr$var24, usr$var27, usr$r)
                                let usr$var29 := 0x3f05c4df7a6664dabe258779bf548eb4007f33601591080b3ecd34aea0e1edc1
                                let usr$a_7 := mload(0x8660)
                                let usr$var30 := usr$q_pow5(usr$a_7)
                                let usr$var31 := mulmod(usr$var29, usr$var30, usr$r)
                                let usr$var32 := addmod(usr$var28, usr$var31, usr$r)
                                let usr$var33 := addmod(mulmod(0, usr$q_trash_tau, usr$r), usr$var32, usr$r)
                                let usr$f_1 := mload(0x8b00)
                                let usr$a_1_next_1 := mload(0x85e0)
                                let usr$var34 := mulmod(usr$a_1_next_1, usr$var0, usr$r)
                                let usr$var35 := addmod(usr$f_1, usr$var34, usr$r)
                                let usr$var36 := 0x5b1fc262a28cbb8bf75d9b1a6edaa74591ec24cd9a209512213cec3a3c0f1a5d
                                let usr$var37 := mulmod(usr$var36, usr$a_0, usr$r)
                                let usr$var38 := addmod(usr$var35, usr$var37, usr$r)
                                let usr$var39 := 0x4d0ea7f9c3fda06d9535b0fdafd8338bd47c2200b284fa71a325ff41ac358028
                                let usr$var40 := mulmod(usr$var39, usr$a_1, usr$r)
                                let usr$var41 := addmod(usr$var38, usr$var40, usr$r)
                                let usr$var42 := 0x26cc223e16f47c20e17cc6069605fa5a8af05ea4f6eb36029a641d23b818eb10
                                let usr$var43 := mulmod(usr$var42, usr$var10, usr$r)
                                let usr$var44 := addmod(usr$var41, usr$var43, usr$r)
                                let usr$var45 := 0x31e823a45e567484c1544e310c0fa5cd66547a8f0dde659ac61698c30e838d25
                                let usr$var46 := mulmod(usr$var45, usr$var14, usr$r)
                                let usr$var47 := addmod(usr$var44, usr$var46, usr$r)
                                let usr$var48 := 0x275a20361ea91992193920270d3e2d1f6361880ac0a439c64bef815d4469ba85
                                let usr$var49 := mulmod(usr$var48, usr$var18, usr$r)
                                let usr$var50 := addmod(usr$var47, usr$var49, usr$r)
                                let usr$var51 := 0x5f3a15bab4ce4097b1edc3a25002694b92395ce355a8a12fe557459d9633f701
                                let usr$var52 := mulmod(usr$var51, usr$var22, usr$r)
                                let usr$var53 := addmod(usr$var50, usr$var52, usr$r)
                                let usr$var54 := 0x301cf56f9b4577112cc4241cddf6484aaadedbf1bbd0f2351adf2e41c2fb2ecd
                                let usr$var55 := mulmod(usr$var54, usr$var26, usr$r)
                                let usr$var56 := addmod(usr$var53, usr$var55, usr$r)
                                let usr$var57 := 0xfdf664da55059fa5a9388c641035d496d0bb519834348b4e2a8fc8c637f1a1f
                                let usr$var58 := mulmod(usr$var57, usr$var30, usr$r)
                                let usr$var59 := addmod(usr$var56, usr$var58, usr$r)
                                let usr$var60 := addmod(mulmod(usr$var33, usr$q_trash_tau, usr$r), usr$var59, usr$r)
                                let usr$f_2 := mload(0x8b20)
                                let usr$var61 := mulmod(usr$a_3, usr$var0, usr$r)
                                let usr$var62 := addmod(usr$f_2, usr$var61, usr$r)
                                let usr$var63 := 0x5e1d3dbecda6214343e24a47f45c5d033197ad01b65a730af95dc57e90c49140
                                let usr$var64 := mulmod(usr$var63, usr$a_0, usr$r)
                                let usr$var65 := addmod(usr$var62, usr$var64, usr$r)
                                let usr$var66 := 0x6bd72f9cfc53af9d931896e77ea5c61244cb6d5fae8954f37dc7b9002f5aa78a
                                let usr$var67 := mulmod(usr$var66, usr$a_1, usr$r)
                                let usr$var68 := addmod(usr$var65, usr$var67, usr$r)
                                let usr$var69 := 0x4997c5aa3a5fa07bcaf880a9054bef831effbd9cd58e46d9bb4fb88ef99de0db
                                let usr$var70 := mulmod(usr$var69, usr$var10, usr$r)
                                let usr$var71 := addmod(usr$var68, usr$var70, usr$r)
                                let usr$var72 := addmod(mulmod(usr$var60, usr$q_trash_tau, usr$r), usr$var71, usr$r)
                                let usr$f_3 := mload(0x8b40)
                                let usr$var73 := mulmod(usr$a_4, usr$var0, usr$r)
                                let usr$var74 := addmod(usr$f_3, usr$var73, usr$r)
                                let usr$var75 := 0x222e83e70453dfee19b402e9fa8dfe2c4987b034d0be3ceb478b3022e97934c1
                                let usr$var76 := mulmod(usr$var75, usr$a_0, usr$r)
                                let usr$var77 := addmod(usr$var74, usr$var76, usr$r)
                                let usr$var78 := 0x26c2cc87f95726b28f33ca03409a460ec987cfe12adae32769e3565865d07191
                                let usr$var79 := mulmod(usr$var78, usr$a_1, usr$r)
                                let usr$var80 := addmod(usr$var77, usr$var79, usr$r)
                                let usr$var81 := 0x4382d0938a760120dd6cef8f3b90a0c38abae475e3d21e39365472b76d780272
                                let usr$var82 := mulmod(usr$var81, usr$var10, usr$r)
                                let usr$var83 := addmod(usr$var80, usr$var82, usr$r)
                                let usr$var84 := mulmod(usr$var69, usr$var14, usr$r)
                                let usr$var85 := addmod(usr$var83, usr$var84, usr$r)
                                let usr$var86 := addmod(mulmod(usr$var72, usr$q_trash_tau, usr$r), usr$var85, usr$r)
                                let usr$f_4 := mload(0x8a40)
                                let usr$var87 := mulmod(usr$a_5, usr$var0, usr$r)
                                let usr$var88 := addmod(usr$f_4, usr$var87, usr$r)
                                let usr$var89 := 0x726df1506749848155630b86ae25a82b281ecd050fe3a52d85a181fa87202e4b
                                let usr$var90 := mulmod(usr$var89, usr$a_0, usr$r)
                                let usr$var91 := addmod(usr$var88, usr$var90, usr$r)
                                let usr$var92 := 0x24822e1af9aa2887c912c87eb0f20bd332330e7e55cd784de67cb407a9f05520
                                let usr$var93 := mulmod(usr$var92, usr$a_1, usr$r)
                                let usr$var94 := addmod(usr$var91, usr$var93, usr$r)
                                let usr$var95 := 0x4e5280109d8f96b8bfb543a6b1af25fb56a9db616af85a90eedc558e3eb1ea29
                                let usr$var96 := mulmod(usr$var95, usr$var10, usr$r)
                                let usr$var97 := addmod(usr$var94, usr$var96, usr$r)
                                let usr$var98 := mulmod(usr$var81, usr$var14, usr$r)
                                let usr$var99 := addmod(usr$var97, usr$var98, usr$r)
                                let usr$var100 := mulmod(usr$var69, usr$var18, usr$r)
                                let usr$var101 := addmod(usr$var99, usr$var100, usr$r)
                                let usr$var102 := addmod(mulmod(usr$var86, usr$q_trash_tau, usr$r), usr$var101, usr$r)
                                let usr$f_5 := mload(0x8a60)
                                let usr$var103 := mulmod(usr$a_6, usr$var0, usr$r)
                                let usr$var104 := addmod(usr$f_5, usr$var103, usr$r)
                                let usr$var105 := 0x2f5908b169c6cf1bd26dcf0f9e5105481f5164f3ece0582bf3098312167751a7
                                let usr$var106 := mulmod(usr$var105, usr$a_0, usr$r)
                                let usr$var107 := addmod(usr$var104, usr$var106, usr$r)
                                let usr$var108 := 0x23a6684b942d726a22e4d5b8d8ff83aeaa773f62600184efe5d033d7c7c6e827
                                let usr$var109 := mulmod(usr$var108, usr$a_1, usr$r)
                                let usr$var110 := addmod(usr$var107, usr$var109, usr$r)
                                let usr$var111 := 0x1981b4b33d6a9dab957b351d981d3323e65da39493af5bc01f7e8ffe17f98d4e
                                let usr$var112 := mulmod(usr$var111, usr$var10, usr$r)
                                let usr$var113 := addmod(usr$var110, usr$var112, usr$r)
                                let usr$var114 := mulmod(usr$var95, usr$var14, usr$r)
                                let usr$var115 := addmod(usr$var113, usr$var114, usr$r)
                                let usr$var116 := mulmod(usr$var81, usr$var18, usr$r)
                                let usr$var117 := addmod(usr$var115, usr$var116, usr$r)
                                let usr$var118 := mulmod(usr$var69, usr$var22, usr$r)
                                let usr$var119 := addmod(usr$var117, usr$var118, usr$r)
                                let usr$var120 := addmod(mulmod(usr$var102, usr$q_trash_tau, usr$r), usr$var119, usr$r)
                                let usr$f_6 := mload(0x8a80)
                                let usr$var121 := mulmod(usr$a_7, usr$var0, usr$r)
                                let usr$var122 := addmod(usr$f_6, usr$var121, usr$r)
                                let usr$var123 := 0x6d05a41959f539a7fc9ec0972ea1e3dbb6fc67dd51daf3414f7fbbb091c7274a
                                let usr$var124 := mulmod(usr$var123, usr$a_0, usr$r)
                                let usr$var125 := addmod(usr$var122, usr$var124, usr$r)
                                let usr$var126 := 0x27e7119226c42a6d19c1541904b99ae40685511ed2e078964b74594d38340849
                                let usr$var127 := mulmod(usr$var126, usr$a_1, usr$r)
                                let usr$var128 := addmod(usr$var125, usr$var127, usr$r)
                                let usr$var129 := 0xd94c46a8456352aa44d7a885ab59e3a36664e6fb25e826f8a4cd79822f0533
                                let usr$var130 := mulmod(usr$var129, usr$var10, usr$r)
                                let usr$var131 := addmod(usr$var128, usr$var130, usr$r)
                                let usr$var132 := mulmod(usr$var111, usr$var14, usr$r)
                                let usr$var133 := addmod(usr$var131, usr$var132, usr$r)
                                let usr$var134 := mulmod(usr$var95, usr$var18, usr$r)
                                let usr$var135 := addmod(usr$var133, usr$var134, usr$r)
                                let usr$var136 := mulmod(usr$var81, usr$var22, usr$r)
                                let usr$var137 := addmod(usr$var135, usr$var136, usr$r)
                                let usr$var138 := mulmod(usr$var69, usr$var26, usr$r)
                                let usr$var139 := addmod(usr$var137, usr$var138, usr$r)
                                let usr$var140 := addmod(mulmod(usr$var120, usr$q_trash_tau, usr$r), usr$var139, usr$r)
                                let usr$f_7 := mload(0x8aa0)
                                let usr$a_2_next_1 := mload(0x8600)
                                let usr$var141 := mulmod(usr$a_2_next_1, usr$var0, usr$r)
                                let usr$var142 := addmod(usr$f_7, usr$var141, usr$r)
                                let usr$var143 := 0x70d8f2a733a64d650faccc9b1c2a766a9544bb3ff1a11ee73cb43947ef386633
                                let usr$var144 := mulmod(usr$var143, usr$a_0, usr$r)
                                let usr$var145 := addmod(usr$var142, usr$var144, usr$r)
                                let usr$var146 := 0x40fa389feb2522bb934881ac9ed749aee2296502af592418c6b5675c0f560261
                                let usr$var147 := mulmod(usr$var146, usr$a_1, usr$r)
                                let usr$var148 := addmod(usr$var145, usr$var147, usr$r)
                                let usr$var149 := 0x1f61345b652161410c5e29f51e301ae56342af824bc110649393d2b911c50d3e
                                let usr$var150 := mulmod(usr$var149, usr$var10, usr$r)
                                let usr$var151 := addmod(usr$var148, usr$var150, usr$r)
                                let usr$var152 := mulmod(usr$var129, usr$var14, usr$r)
                                let usr$var153 := addmod(usr$var151, usr$var152, usr$r)
                                let usr$var154 := mulmod(usr$var111, usr$var18, usr$r)
                                let usr$var155 := addmod(usr$var153, usr$var154, usr$r)
                                let usr$var156 := mulmod(usr$var95, usr$var22, usr$r)
                                let usr$var157 := addmod(usr$var155, usr$var156, usr$r)
                                let usr$var158 := mulmod(usr$var81, usr$var26, usr$r)
                                let usr$var159 := addmod(usr$var157, usr$var158, usr$r)
                                let usr$var160 := mulmod(usr$var69, usr$var30, usr$r)
                                let usr$var161 := addmod(usr$var159, usr$var160, usr$r)
                                let usr$var162 := addmod(mulmod(usr$var140, usr$q_trash_tau, usr$r), usr$var161, usr$r)
                                let usr$f_26 := mload(0x8c20)
                                let usr$q_trash_one_minus_selector := addmod(1, sub(usr$r, usr$f_26), usr$r)
                                let usr$q_trash_scaled := mulmod(usr$q_trash_one_minus_selector, mload(0x91a0), usr$r)
                                let usr$q_trash_eval := addmod(usr$var162, sub(usr$r, usr$q_trash_scaled), usr$r)
                                mstore(0xa300, mulmod(mload(0xa300), usr$y, usr$r))
                                mstore(0xa300, addmod(mload(0xa300), usr$q_trash_eval, usr$r))
                            }
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x00)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0600)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x20)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x05e0)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x40)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0580)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x60)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0520)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x80)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x04c0)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0xa0)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0460)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0xc0)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0400)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0xe0)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x03a0)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x0100)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0340)), usr$r))
                        }
                        {
                            let usr$q_sel_ptr := add(41408, 0x0120)
                            mstore(usr$q_sel_ptr, mulmod(mload(usr$q_sel_ptr), mload(add(0xa340, 0x0280)), usr$r))
                        }
                        let usr$linearization_expected_eval := addmod(0, sub(usr$r, mload(0xa300)), usr$r)
                        mstore(28032, usr$linearization_expected_eval)
                        pop(usr$y)
                    }
                    {
                        let usr$x := mload(27168)
                        let usr$k := 20
                        let usr$x_pow_2i := usr$x
                        let usr$x_pow_2i_minus1 := 1
                        for { let usr$idx := 0 }
                        lt(usr$idx, usr$k)
                        { usr$idx := add(usr$idx, 1) }
                        {
                            usr$x_pow_2i_minus1 := mulmod(mulmod(usr$x_pow_2i_minus1, usr$x_pow_2i_minus1, usr$r), usr$x, usr$r)
                            usr$x_pow_2i := mulmod(usr$x_pow_2i, usr$x_pow_2i, usr$r)
                        }
                        let usr$x_split := usr$x_pow_2i_minus1
                        let usr$one_minus_x_n := addmod(1, sub(usr$r, usr$x_pow_2i), usr$r)
                        mstore(28064, usr$x_split)
                        mstore(add(28064, 0x20), usr$one_minus_x_n)
                    }
                    {
                        {
                            let usr$x := mload(27168)
                            let usr$omega := mload(10112)
                            let usr$omega_inv := mload(10144)
                            let usr$x_pow_of_omega := usr$x
                            mstore(add(28672, 0x40), usr$x_pow_of_omega)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega, usr$r)
                            mstore(add(28672, 0x60), usr$x_pow_of_omega)
                            usr$x_pow_of_omega := usr$x
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            mstore(add(28672, 0x20), usr$x_pow_of_omega)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            usr$x_pow_of_omega := mulmod(usr$x_pow_of_omega, usr$omega_inv, usr$r)
                            mstore(add(28672, 0x0), usr$x_pow_of_omega)
                        }
                        {
                            let usr$x1 := mload(27200)
                            mstore(29568, 1)
                            let usr$acc := 1
                            let usr$p := 29568
                            for { let usr$i := 0 } lt(usr$i, 0x2a) { usr$i := add(usr$i, 1) }
                            {
                                usr$p := add(usr$p, 0x20)
                                usr$acc := mulmod(usr$acc, usr$x1, usr$r)
                                mstore(usr$p, and(usr$acc, 0xffffffffffffffffffffffffffffffff))
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
                            let usr$q_eval_set_0 := mload(0x8a00)
                            let usr$pow_p := add(29568, 0x20)
                            let usr$eval_p := add(0xa300, 0x20)
                            for { let usr$i := 1 } lt(usr$i, 0x2b) { usr$i := add(usr$i, 1) }
                            {
                                let usr$pow := mload(usr$pow_p)
                                usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(mload(usr$eval_p)), usr$pow, usr$r), usr$r)
                                usr$pow_p := add(usr$pow_p, 0x20)
                                usr$eval_p := add(usr$eval_p, 0x20)
                            }
                            mstore(add(31648, 0x0), usr$q_eval_set_0)
                        }
                        {
                            let usr$q_eval_set_0 := mload(0x86e0)
                            let usr$q_eval_set_1 := mload(0x89a0)
                            usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(0x8700), mload(add(29568, 0x20)), usr$r), usr$r)
                            usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(0x89c0), mload(add(29568, 0x20)), usr$r), usr$r)
                            usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(0x8720), mload(add(29568, 0x40)), usr$r), usr$r)
                            usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(0x89e0), mload(add(29568, 0x40)), usr$r), usr$r)
                            mstore(add(31648, 0x20), usr$q_eval_set_0)
                            mstore(add(31648, 0x40), usr$q_eval_set_1)
                        }
                        {
                            let usr$q_eval_set_0 := mload(0x9060)
                            let usr$q_eval_set_1 := mload(0x9080)
                            usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(0x90e0), mload(add(29568, 0x20)), usr$r), usr$r)
                            usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(0x9100), mload(add(29568, 0x20)), usr$r), usr$r)
                            usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(0x9160), mload(add(29568, 0x40)), usr$r), usr$r)
                            usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(0x9180), mload(add(29568, 0x40)), usr$r), usr$r)
                            mstore(add(31648, 0x60), usr$q_eval_set_0)
                            mstore(add(31648, 0x80), usr$q_eval_set_1)
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
                            let usr$q_eval_set_0 := mload(0x8520)
                            let usr$q_eval_set_1 := mload(0x85c0)
                            let usr$q_eval_set_2 := mload(0x8840)
                            let usr$pow_p := add(29568, 0x20)
                            let usr$eval_p := add(0xa300, 0x60)
                            for { let usr$i := 1 } lt(usr$i, 0xb) { usr$i := add(usr$i, 1) }
                            {
                                let usr$pow := mload(usr$pow_p)
                                usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(mload(usr$eval_p)), usr$pow, usr$r), usr$r)
                                usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(mload(add(usr$eval_p, 0x20))), usr$pow, usr$r), usr$r)
                                usr$q_eval_set_2 := addmod(usr$q_eval_set_2, mulmod(mload(mload(add(usr$eval_p, 0x40))), usr$pow, usr$r), usr$r)
                                usr$pow_p := add(usr$pow_p, 0x20)
                                usr$eval_p := add(usr$eval_p, 0x60)
                            }
                            mstore(add(31648, 0xa0), usr$q_eval_set_0)
                            mstore(add(31648, 0xc0), usr$q_eval_set_1)
                            mstore(add(31648, 0xe0), usr$q_eval_set_2)
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
                            let usr$q_eval_set_0 := mload(0x8e80)
                            let usr$q_eval_set_1 := mload(0x8ea0)
                            let usr$q_eval_set_2 := mload(0x8ec0)
                            let usr$pow_p := add(29568, 0x20)
                            let usr$eval_p := add(0xa300, 0x60)
                            for { let usr$i := 1 } lt(usr$i, 0x5) { usr$i := add(usr$i, 1) }
                            {
                                let usr$pow := mload(usr$pow_p)
                                usr$q_eval_set_0 := addmod(usr$q_eval_set_0, mulmod(mload(mload(usr$eval_p)), usr$pow, usr$r), usr$r)
                                usr$q_eval_set_1 := addmod(usr$q_eval_set_1, mulmod(mload(mload(add(usr$eval_p, 0x20))), usr$pow, usr$r), usr$r)
                                usr$q_eval_set_2 := addmod(usr$q_eval_set_2, mulmod(mload(mload(add(usr$eval_p, 0x40))), usr$pow, usr$r), usr$r)
                                usr$pow_p := add(usr$pow_p, 0x20)
                                usr$eval_p := add(usr$eval_p, 0x60)
                            }
                            mstore(add(31648, 0x100), usr$q_eval_set_0)
                            mstore(add(31648, 0x120), usr$q_eval_set_1)
                            mstore(add(31648, 0x140), usr$q_eval_set_2)
                        }
                        {
                            let usr$x2 := mload(27232)
                            let usr$x3 := mload(27264)
                            let usr$f_eval := 0
                            let usr$Q_EVAL_CPTR := mload(33440)
                            let usr$rot_pt_0 := mload(add(28672, 0x0))
                            let usr$rot_pt_1 := mload(add(28672, 0x20))
                            let usr$rot_pt_2 := mload(add(28672, 0x40))
                            let usr$rot_pt_3 := mload(add(28672, 0x60))
                            {
                                let usr$dx_0 := addmod(usr$x3, sub(usr$r, usr$rot_pt_2), usr$r)
                                let usr$dx_1 := addmod(usr$x3, sub(usr$r, usr$rot_pt_3), usr$r)
                                let usr$dx_2 := addmod(usr$x3, sub(usr$r, usr$rot_pt_0), usr$r)
                                let usr$lbasis_0 := 1
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_3), usr$r), usr$r)
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_0), usr$r), usr$r)
                                let usr$lbasis_1 := 1
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_3, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_3, sub(usr$r, usr$rot_pt_0), usr$r), usr$r)
                                let usr$lbasis_2 := 1
                                usr$lbasis_2 := mulmod(usr$lbasis_2, addmod(usr$rot_pt_0, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                usr$lbasis_2 := mulmod(usr$lbasis_2, addmod(usr$rot_pt_0, sub(usr$r, usr$rot_pt_3), usr$r), usr$r)
                                let usr$bp_0 := usr$dx_0
                                let usr$bp_1 := mulmod(usr$bp_0, usr$dx_1, usr$r)
                                let usr$bp_2 := mulmod(usr$bp_1, usr$dx_2, usr$r)
                                let usr$bp_3 := mulmod(usr$bp_2, usr$lbasis_0, usr$r)
                                let usr$bp_4 := mulmod(usr$bp_3, usr$lbasis_1, usr$r)
                                let usr$bp_5 := mulmod(usr$bp_4, usr$lbasis_2, usr$r)
                                let usr$bq := usr$scalar_inv(usr$bp_5)
                                let usr$lbasis_inv_2 := mulmod(usr$bq, usr$bp_4, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_2, usr$r)
                                let usr$lbasis_inv_1 := mulmod(usr$bq, usr$bp_3, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_1, usr$r)
                                let usr$lbasis_inv_0 := mulmod(usr$bq, usr$bp_2, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_0, usr$r)
                                let usr$dx_inv_2 := mulmod(usr$bq, usr$bp_1, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_2, usr$r)
                                let usr$dx_inv_1 := mulmod(usr$bq, usr$bp_0, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_1, usr$r)
                                let usr$dx_inv_0 := usr$bq
                                let usr$den_inv := usr$dx_inv_0
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_1, usr$r)
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_2, usr$r)
                                let usr$eval := mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x80)), usr$den_inv, usr$r)
                                let usr$term_0 := mulmod(mulmod(mload(add(31648, 0x100)), usr$dx_inv_0, usr$r), usr$lbasis_inv_0, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_0), usr$r)
                                let usr$term_1 := mulmod(mulmod(mload(add(31648, 0x120)), usr$dx_inv_1, usr$r), usr$lbasis_inv_1, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_1), usr$r)
                                let usr$term_2 := mulmod(mulmod(mload(add(31648, 0x140)), usr$dx_inv_2, usr$r), usr$lbasis_inv_2, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_2), usr$r)
                                usr$f_eval := addmod(mulmod(usr$f_eval, usr$x2, usr$r), usr$eval, usr$r)
                            }
                            {
                                let usr$dx_0 := addmod(usr$x3, sub(usr$r, usr$rot_pt_2), usr$r)
                                let usr$dx_1 := addmod(usr$x3, sub(usr$r, usr$rot_pt_3), usr$r)
                                let usr$dx_2 := addmod(usr$x3, sub(usr$r, usr$rot_pt_1), usr$r)
                                let usr$lbasis_0 := 1
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_3), usr$r), usr$r)
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_1), usr$r), usr$r)
                                let usr$lbasis_1 := 1
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_3, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_3, sub(usr$r, usr$rot_pt_1), usr$r), usr$r)
                                let usr$lbasis_2 := 1
                                usr$lbasis_2 := mulmod(usr$lbasis_2, addmod(usr$rot_pt_1, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                usr$lbasis_2 := mulmod(usr$lbasis_2, addmod(usr$rot_pt_1, sub(usr$r, usr$rot_pt_3), usr$r), usr$r)
                                let usr$bp_0 := usr$dx_0
                                let usr$bp_1 := mulmod(usr$bp_0, usr$dx_1, usr$r)
                                let usr$bp_2 := mulmod(usr$bp_1, usr$dx_2, usr$r)
                                let usr$bp_3 := mulmod(usr$bp_2, usr$lbasis_0, usr$r)
                                let usr$bp_4 := mulmod(usr$bp_3, usr$lbasis_1, usr$r)
                                let usr$bp_5 := mulmod(usr$bp_4, usr$lbasis_2, usr$r)
                                let usr$bq := usr$scalar_inv(usr$bp_5)
                                let usr$lbasis_inv_2 := mulmod(usr$bq, usr$bp_4, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_2, usr$r)
                                let usr$lbasis_inv_1 := mulmod(usr$bq, usr$bp_3, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_1, usr$r)
                                let usr$lbasis_inv_0 := mulmod(usr$bq, usr$bp_2, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_0, usr$r)
                                let usr$dx_inv_2 := mulmod(usr$bq, usr$bp_1, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_2, usr$r)
                                let usr$dx_inv_1 := mulmod(usr$bq, usr$bp_0, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_1, usr$r)
                                let usr$dx_inv_0 := usr$bq
                                let usr$den_inv := usr$dx_inv_0
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_1, usr$r)
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_2, usr$r)
                                let usr$eval := mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x60)), usr$den_inv, usr$r)
                                let usr$term_0 := mulmod(mulmod(mload(add(31648, 0xa0)), usr$dx_inv_0, usr$r), usr$lbasis_inv_0, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_0), usr$r)
                                let usr$term_1 := mulmod(mulmod(mload(add(31648, 0xc0)), usr$dx_inv_1, usr$r), usr$lbasis_inv_1, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_1), usr$r)
                                let usr$term_2 := mulmod(mulmod(mload(add(31648, 0xe0)), usr$dx_inv_2, usr$r), usr$lbasis_inv_2, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_2), usr$r)
                                usr$f_eval := addmod(mulmod(usr$f_eval, usr$x2, usr$r), usr$eval, usr$r)
                            }
                            {
                                let usr$dx_0 := addmod(usr$x3, sub(usr$r, usr$rot_pt_2), usr$r)
                                let usr$dx_1 := addmod(usr$x3, sub(usr$r, usr$rot_pt_3), usr$r)
                                let usr$lbasis_0 := 1
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_3), usr$r), usr$r)
                                let usr$lbasis_1 := 1
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_3, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                let usr$bp_0 := usr$dx_0
                                let usr$bp_1 := mulmod(usr$bp_0, usr$dx_1, usr$r)
                                let usr$bp_2 := mulmod(usr$bp_1, usr$lbasis_0, usr$r)
                                let usr$bp_3 := mulmod(usr$bp_2, usr$lbasis_1, usr$r)
                                let usr$bq := usr$scalar_inv(usr$bp_3)
                                let usr$lbasis_inv_1 := mulmod(usr$bq, usr$bp_2, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_1, usr$r)
                                let usr$lbasis_inv_0 := mulmod(usr$bq, usr$bp_1, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_0, usr$r)
                                let usr$dx_inv_1 := mulmod(usr$bq, usr$bp_0, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_1, usr$r)
                                let usr$dx_inv_0 := usr$bq
                                let usr$den_inv := usr$dx_inv_0
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_1, usr$r)
                                let usr$eval := mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x40)), usr$den_inv, usr$r)
                                let usr$term_0 := mulmod(mulmod(mload(add(31648, 0x60)), usr$dx_inv_0, usr$r), usr$lbasis_inv_0, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_0), usr$r)
                                let usr$term_1 := mulmod(mulmod(mload(add(31648, 0x80)), usr$dx_inv_1, usr$r), usr$lbasis_inv_1, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_1), usr$r)
                                usr$f_eval := addmod(mulmod(usr$f_eval, usr$x2, usr$r), usr$eval, usr$r)
                            }
                            {
                                let usr$dx_0 := addmod(usr$x3, sub(usr$r, usr$rot_pt_2), usr$r)
                                let usr$dx_1 := addmod(usr$x3, sub(usr$r, usr$rot_pt_1), usr$r)
                                let usr$lbasis_0 := 1
                                usr$lbasis_0 := mulmod(usr$lbasis_0, addmod(usr$rot_pt_2, sub(usr$r, usr$rot_pt_1), usr$r), usr$r)
                                let usr$lbasis_1 := 1
                                usr$lbasis_1 := mulmod(usr$lbasis_1, addmod(usr$rot_pt_1, sub(usr$r, usr$rot_pt_2), usr$r), usr$r)
                                let usr$bp_0 := usr$dx_0
                                let usr$bp_1 := mulmod(usr$bp_0, usr$dx_1, usr$r)
                                let usr$bp_2 := mulmod(usr$bp_1, usr$lbasis_0, usr$r)
                                let usr$bp_3 := mulmod(usr$bp_2, usr$lbasis_1, usr$r)
                                let usr$bq := usr$scalar_inv(usr$bp_3)
                                let usr$lbasis_inv_1 := mulmod(usr$bq, usr$bp_2, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_1, usr$r)
                                let usr$lbasis_inv_0 := mulmod(usr$bq, usr$bp_1, usr$r)
                                usr$bq := mulmod(usr$bq, usr$lbasis_0, usr$r)
                                let usr$dx_inv_1 := mulmod(usr$bq, usr$bp_0, usr$r)
                                usr$bq := mulmod(usr$bq, usr$dx_1, usr$r)
                                let usr$dx_inv_0 := usr$bq
                                let usr$den_inv := usr$dx_inv_0
                                usr$den_inv := mulmod(usr$den_inv, usr$dx_inv_1, usr$r)
                                let usr$eval := mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x20)), usr$den_inv, usr$r)
                                let usr$term_0 := mulmod(mulmod(mload(add(31648, 0x20)), usr$dx_inv_0, usr$r), usr$lbasis_inv_0, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_0), usr$r)
                                let usr$term_1 := mulmod(mulmod(mload(add(31648, 0x40)), usr$dx_inv_1, usr$r), usr$lbasis_inv_1, usr$r)
                                usr$eval := addmod(usr$eval, sub(usr$r, usr$term_1), usr$r)
                                usr$f_eval := addmod(mulmod(usr$f_eval, usr$x2, usr$r), usr$eval, usr$r)
                            }
                            {
                                let usr$dx0 := addmod(usr$x3, sub(usr$r, usr$rot_pt_2), usr$r)
                                let usr$dx0_inv := usr$scalar_inv(usr$dx0)
                                let usr$eval := mulmod(addmod(calldataload(add(usr$Q_EVAL_CPTR, 0x0)), sub(usr$r, mload(add(31648, 0x0))), usr$r), usr$dx0_inv, usr$r)
                                usr$f_eval := addmod(mulmod(usr$f_eval, usr$x2, usr$r), usr$eval, usr$r)
                            }
                            mstore(28224, usr$f_eval)
                        }
                        {
                            let usr$x4 := mload(27296)
                            let usr$lin_x_split := mload(28064)
                            let usr$lin_one_minus_x_n := mload(add(28064, 0x20))
                            let usr$Q_EVAL_CPTR := mload(33440)
                            let usr$x4_pow_full := 1
                            usr$x4_pow_full := mulmod(usr$x4_pow_full, usr$x4, usr$r)
                            let usr$x4_pow_1 := and(usr$x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            usr$x4_pow_full := mulmod(usr$x4_pow_full, usr$x4, usr$r)
                            let usr$x4_pow_2 := and(usr$x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            usr$x4_pow_full := mulmod(usr$x4_pow_full, usr$x4, usr$r)
                            let usr$x4_pow_3 := and(usr$x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            usr$x4_pow_full := mulmod(usr$x4_pow_full, usr$x4, usr$r)
                            let usr$x4_pow_4 := and(usr$x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            usr$x4_pow_full := mulmod(usr$x4_pow_full, usr$x4, usr$r)
                            let usr$x4_pow_5 := and(usr$x4_pow_full, 0xffffffffffffffffffffffffffffffff)
                            let usr$v := calldataload(usr$Q_EVAL_CPTR)
                            usr$v := addmod(usr$v, mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x20)), usr$x4_pow_1, usr$r), usr$r)
                            usr$v := addmod(usr$v, mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x40)), usr$x4_pow_2, usr$r), usr$r)
                            usr$v := addmod(usr$v, mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x60)), usr$x4_pow_3, usr$r), usr$r)
                            usr$v := addmod(usr$v, mulmod(calldataload(add(usr$Q_EVAL_CPTR, 0x80)), usr$x4_pow_4, usr$r), usr$r)
                            usr$v := addmod(usr$v, mulmod(mload(28224), usr$x4_pow_5, usr$r), usr$r)
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
                            let usr$lin_query_scalar_41 := mload(add(29568, 0x540))
                            let usr$lin_cur_scalar_41 := mulmod(usr$lin_query_scalar_41, usr$lin_one_minus_x_n, usr$r)
                            mcopy(0xbca0, add(40896, 0x0), 0x80)
                            mstore(0xbd20, usr$lin_cur_scalar_41)
                            usr$lin_cur_scalar_41 := mulmod(usr$lin_cur_scalar_41, usr$lin_x_split, usr$r)
                            mcopy(0xbd40, add(40896, 0x80), 0x80)
                            mstore(0xbdc0, usr$lin_cur_scalar_41)
                            usr$lin_cur_scalar_41 := mulmod(usr$lin_cur_scalar_41, usr$lin_x_split, usr$r)
                            mcopy(0xbde0, add(40896, 0x100), 0x80)
                            mstore(0xbe60, usr$lin_cur_scalar_41)
                            usr$lin_cur_scalar_41 := mulmod(usr$lin_cur_scalar_41, usr$lin_x_split, usr$r)
                            mcopy(0xbe80, add(40896, 0x180), 0x80)
                            mstore(0xbf00, usr$lin_cur_scalar_41)
                            mcopy(0xbf20, 0x5a00, 0x80)
                            mstore(0xbfa0, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x0)), usr$r))
                            mcopy(0xbfc0, 0x5a80, 0x80)
                            mstore(0xc040, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x20)), usr$r))
                            mcopy(0xc060, 0x5b00, 0x80)
                            mstore(0xc0e0, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x40)), usr$r))
                            mcopy(0xc100, 0x5c00, 0x80)
                            mstore(0xc180, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x60)), usr$r))
                            mcopy(0xc1a0, 0x5c80, 0x80)
                            mstore(0xc220, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x80)), usr$r))
                            mcopy(0xc240, 0x5d00, 0x80)
                            mstore(0xc2c0, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0xa0)), usr$r))
                            mcopy(0xc2e0, 0x5d80, 0x80)
                            mstore(0xc360, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0xc0)), usr$r))
                            mcopy(0xc380, 0x5e00, 0x80)
                            mstore(0xc400, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0xe0)), usr$r))
                            mcopy(0xc420, 0x5e80, 0x80)
                            mstore(0xc4a0, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x100)), usr$r))
                            mcopy(0xc4c0, 0x5f80, 0x80)
                            mstore(0xc540, mulmod(usr$lin_query_scalar_41, mload(add(41408, 0x120)), usr$r))
                            mcopy(0xc560, 0x9740, 0x80)
                            mstore(0xc5e0, usr$x4_pow_1)
                            mcopy(0xc600, 0x97c0, 0x80)
                            mstore(0xc680, mulmod(mload(add(29568, 0x20)), usr$x4_pow_1, usr$r))
                            mcopy(0xc6a0, 0x9840, 0x80)
                            mstore(0xc720, mulmod(mload(add(29568, 0x40)), usr$x4_pow_1, usr$r))
                            mcopy(0xc740, 0x9cc0, 0x80)
                            mstore(0xc7c0, usr$x4_pow_2)
                            mcopy(0xc7e0, 0x9e40, 0x80)
                            mstore(0xc860, mulmod(mload(add(29568, 0x20)), usr$x4_pow_2, usr$r))
                            mcopy(0xc880, 0x9ec0, 0x80)
                            mstore(0xc900, mulmod(mload(add(29568, 0x40)), usr$x4_pow_2, usr$r))
                            mcopy(0xc920, 0x91c0, 0x80)
                            mstore(0xc9a0, usr$x4_pow_3)
                            mcopy(0xc9c0, 0x9240, 0x80)
                            mstore(0xca40, mulmod(mload(add(29568, 0x20)), usr$x4_pow_3, usr$r))
                            mcopy(0xca60, 0x92c0, 0x80)
                            mstore(0xcae0, mulmod(mload(add(29568, 0x40)), usr$x4_pow_3, usr$r))
                            mcopy(0xcb00, 0x9340, 0x80)
                            mstore(0xcb80, mulmod(mload(add(29568, 0x60)), usr$x4_pow_3, usr$r))
                            mcopy(0xcba0, 0x93c0, 0x80)
                            mstore(0xcc20, mulmod(mload(add(29568, 0x80)), usr$x4_pow_3, usr$r))
                            mcopy(0xcc40, 0x9440, 0x80)
                            mstore(0xccc0, mulmod(mload(add(29568, 0xa0)), usr$x4_pow_3, usr$r))
                            mcopy(0xcce0, 0x94c0, 0x80)
                            mstore(0xcd60, mulmod(mload(add(29568, 0xc0)), usr$x4_pow_3, usr$r))
                            mcopy(0xcd80, 0x9540, 0x80)
                            mstore(0xce00, mulmod(mload(add(29568, 0xe0)), usr$x4_pow_3, usr$r))
                            mcopy(0xce20, 0x95c0, 0x80)
                            mstore(0xcea0, mulmod(mload(add(29568, 0x100)), usr$x4_pow_3, usr$r))
                            mcopy(0xcec0, 0x9640, 0x80)
                            mstore(0xcf40, mulmod(mload(add(29568, 0x120)), usr$x4_pow_3, usr$r))
                            mcopy(0xcf60, 0x96c0, 0x80)
                            mstore(0xcfe0, mulmod(mload(add(29568, 0x140)), usr$x4_pow_3, usr$r))
                            mcopy(0xd000, 0x9a40, 0x80)
                            mstore(0xd080, usr$x4_pow_4)
                            mcopy(0xd0a0, 0x9ac0, 0x80)
                            mstore(0xd120, mulmod(mload(add(29568, 0x20)), usr$x4_pow_4, usr$r))
                            mcopy(0xd140, 0x9b40, 0x80)
                            mstore(0xd1c0, mulmod(mload(add(29568, 0x40)), usr$x4_pow_4, usr$r))
                            mcopy(0xd1e0, 0x9bc0, 0x80)
                            mstore(0xd260, mulmod(mload(add(29568, 0x60)), usr$x4_pow_4, usr$r))
                            mcopy(0xd280, 0x9c40, 0x80)
                            mstore(0xd300, mulmod(mload(add(29568, 0x80)), usr$x4_pow_4, usr$r))
                            mcopy(0xd320, 27328, 0x80)
                            mstore(0xd3a0, usr$x4_pow_5)
                            if usr$success
                            {
                                usr$success := staticcall(gas(), 0x0c, 0xa300, 0x30c0, 28288, 0x80)
                                usr$success := and(usr$success, eq(returndatasize(), 0x80))
                            }
                            mstore(28256, usr$v)
                        }
                        {
                            mcopy(28416, 27456, 0x80)
                            mcopy(0x80, 10336, 0x80)
                            mstore(0x100, addmod(0, sub(usr$r, mload(28256)), usr$r))
                            if usr$success
                            {
                                usr$success := staticcall(gas(), 0x0c, 0x80, 0xa0, 0x80, 0x80)
                                usr$success := and(usr$success, eq(returndatasize(), 0x80))
                            }
                            mcopy(0x100, 28288, 0x80)
                            if usr$success
                            {
                                usr$success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                                usr$success := and(usr$success, eq(returndatasize(), 0x80))
                            }
                            mcopy(0x100, 27456, 0x80)
                            mstore(0x180, mload(27264))
                            if usr$success
                            {
                                usr$success := staticcall(gas(), 0x0c, 0x100, 0xa0, 0x100, 0x80)
                                usr$success := and(usr$success, eq(returndatasize(), 0x80))
                            }
                            if usr$success
                            {
                                usr$success := staticcall(gas(), 0x0b, 0x80, 0x100, 0x80, 0x80)
                                usr$success := and(usr$success, eq(returndatasize(), 0x80))
                            }
                            mcopy(28544, 0x80, 0x80)
                        }
                    }
                    {
                        let usr$batch_ptr := 0x0100
                        mstore(usr$batch_ptr, 0x70616972696e672d62617463682d6163632d6b7a670000000000000000)
                        mcopy(add(usr$batch_ptr, 0x20), 28544, 0x80)
                        mcopy(add(usr$batch_ptr, 0xa0), 28416, 0x80)
                        mcopy(add(usr$batch_ptr, 0x0120), 27712, 0x80)
                        mcopy(add(usr$batch_ptr, 0x01a0), 27584, 0x80)
                        let usr$acc_pair_alpha := mod(keccak256(usr$batch_ptr, 0x0220), usr$r)
                        if iszero(usr$acc_pair_alpha) { usr$acc_pair_alpha := 1 }
                        mcopy(usr$batch_ptr, 27712, 0x80)
                        mstore(add(usr$batch_ptr, 0x80), usr$acc_pair_alpha)
                        if usr$success
                        {
                            usr$success := staticcall(gas(), 0x0c, usr$batch_ptr, 0xa0, usr$batch_ptr, 0x80)
                            usr$success := and(usr$success, eq(returndatasize(), 0x80))
                        }
                        mcopy(add(usr$batch_ptr, 0x80), 28544, 0x80)
                        if usr$success
                        {
                            usr$success := staticcall(gas(), 0x0b, usr$batch_ptr, 0x0100, 28544, 0x80)
                            usr$success := and(usr$success, eq(returndatasize(), 0x80))
                        }
                        mcopy(usr$batch_ptr, 27584, 0x80)
                        mstore(add(usr$batch_ptr, 0x80), usr$acc_pair_alpha)
                        if usr$success
                        {
                            usr$success := staticcall(gas(), 0x0c, usr$batch_ptr, 0xa0, usr$batch_ptr, 0x80)
                            usr$success := and(usr$success, eq(returndatasize(), 0x80))
                        }
                        mcopy(add(usr$batch_ptr, 0x80), 28416, 0x80)
                        if usr$success
                        {
                            usr$success := staticcall(gas(), 0x0b, usr$batch_ptr, 0x0100, 28416, 0x80)
                            usr$success := and(usr$success, eq(returndatasize(), 0x80))
                        }
                    }
                    if iszero(usr$success) { revert(0, 0) }
                    usr$success := usr$ec_pairing(usr$success, 28544, 28416)
                    mstore(128, 1)
                    return(128, 0x20)
                }

            }
            /// @src 0:2063:206619  "contract Halo2Verifier {..."

        }

        data ".metadata" hex"a164736f6c634300081e000a"
    }

}

