IR:

/// @use-src 0:"A.sol"
object "A_64" {
    code {
        /// @src 0:685:1557  "contract A {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_A_64()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("A_64_deployed"), datasize("A_64_deployed"))

        return(_1, datasize("A_64_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:685:1557  "contract A {..."
        function constructor_A_64() {

            /// @src 0:685:1557  "contract A {..."

        }
        /// @src 0:685:1557  "contract A {..."

    }
    /// @use-src 0:"A.sol"
    object "A_64_deployed" {
        code {
            /// @src 0:685:1557  "contract A {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x13d1aa2e
                {
                    // f(uint256,uint256)

                    external_fun_f_63()
                }

                case 0x51973ec9
                {
                    // log()

                    external_fun_log_7()
                }

                case 0x61bc221a
                {
                    // counter()

                    external_fun_counter_3()
                }

                case 0x890eba68
                {
                    // flag()

                    external_fun_flag_5()
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

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function validator_revert_t_uint256(value) {
                if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
            }

            function abi_decode_t_uint256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_uint256(value)
            }

            function abi_decode_tuple_t_uint256t_uint256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(headStart , value0, value1) -> tail {
                tail := add(headStart, 64)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

                abi_encode_t_uint256_to_t_uint256_fromStack(value1,  add(headStart, 32))

            }

            function external_fun_f_63() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
                let ret_0, ret_1 :=  fun_f_63(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256_t_uint256__to_t_uint256_t_uint256__fromStack(memPos , ret_0, ret_1)
                return(memPos, sub(memEnd, memPos))

            }

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            function shift_right_unsigned_dynamic(bits, value) -> newValue {
                newValue :=

                shr(bits, value)

            }

            function cleanup_from_storage_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function extract_from_storage_value_dynamict_uint256(slot_value, offset) -> value {
                value := cleanup_from_storage_t_uint256(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_uint256(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_uint256(sload(slot), offset)

            }

            /// @ast-id 7
            /// @src 0:838:856  "uint256 public log"
            function getter_fun_log_7() -> ret {

                let slot := 2
                let offset := 0

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:685:1557  "contract A {..."

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_log_7() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_log_7()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            /// @ast-id 3
            /// @src 0:784:806  "uint256 public counter"
            function getter_fun_counter_3() -> ret {

                let slot := 0
                let offset := 0

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:685:1557  "contract A {..."

            function external_fun_counter_3() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_counter_3()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function cleanup_from_storage_t_bool(value) -> cleaned {
                cleaned := and(value, 0xff)
            }

            function extract_from_storage_value_dynamict_bool(slot_value, offset) -> value {
                value := cleanup_from_storage_t_bool(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_bool(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_bool(sload(slot), offset)

            }

            /// @ast-id 5
            /// @src 0:812:832  "bool     public flag"
            function getter_fun_flag_5() -> ret {

                let slot := 1
                let offset := 0

                ret := read_from_storage_split_dynamic_t_bool(slot, offset)

            }
            /// @src 0:685:1557  "contract A {..."

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

            function external_fun_flag_5() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_flag_5()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_bool__to_t_bool__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function zero_value_for_split_t_uint256() -> ret {
                ret := 0
            }

            function shift_right_0_unsigned(value) -> newValue {
                newValue :=

                shr(0, value)

            }

            function extract_from_storage_value_offset_0t_uint256(slot_value) -> value {
                value := cleanup_from_storage_t_uint256(shift_right_0_unsigned(slot_value))
            }

            function read_from_storage_split_offset_0_t_uint256(slot) -> value {
                value := extract_from_storage_value_offset_0t_uint256(sload(slot))

            }

            function cleanup_t_rational_1_by_1(value) -> cleaned {
                cleaned := value
            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_rational_1_by_1_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_rational_1_by_1(value)))
            }

            function panic_error_0x11() {
                mstore(0, 35408467139433450592217433187231851964531694900788300625387963629091585785856)
                mstore(4, 0x11)
                revert(0, 0x24)
            }

            function checked_add_t_uint256(x, y) -> sum {
                x := cleanup_t_uint256(x)
                y := cleanup_t_uint256(y)
                sum := add(x, y)

                if gt(x, sum) { panic_error_0x11() }

            }

            function shift_left_0(value) -> newValue {
                newValue :=

                shl(0, value)

            }

            function update_byte_slice_32_shift_0(value, toInsert) -> result {
                let mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
                toInsert := shift_left_0(toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }

            function convert_t_uint256_to_t_uint256(value) -> converted {
                converted := cleanup_t_uint256(identity(cleanup_t_uint256(value)))
            }

            function prepare_store_t_uint256(value) -> ret {
                ret := value
            }

            function update_storage_value_offset_0t_uint256_to_t_uint256(slot, value_0) {
                let convertedValue_0 := convert_t_uint256_to_t_uint256(value_0)
                sstore(slot, update_byte_slice_32_shift_0(sload(slot), prepare_store_t_uint256(convertedValue_0)))
            }

            function update_byte_slice_1_shift_0(value, toInsert) -> result {
                let mask := 255
                toInsert := shift_left_0(toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }

            function convert_t_bool_to_t_bool(value) -> converted {
                converted := cleanup_t_bool(value)
            }

            function prepare_store_t_bool(value) -> ret {
                ret := value
            }

            function update_storage_value_offset_0t_bool_to_t_bool(slot, value_0) {
                let convertedValue_0 := convert_t_bool_to_t_bool(value_0)
                sstore(slot, update_byte_slice_1_shift_0(sload(slot), prepare_store_t_bool(convertedValue_0)))
            }

            /// @ast-id 63
            /// @src 0:863:1555  "function f(uint256 x, uint256 y) external returns (uint256, uint256) {..."
            function fun_f_63(var_x_9, var_y_11) -> var__14, var__16 {
                /// @src 0:914:921  "uint256"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var__14 := zero_t_uint256_1
                /// @src 0:923:930  "uint256"
                let zero_t_uint256_2 := zero_value_for_split_t_uint256()
                var__16 := zero_t_uint256_2

                /// @src 0:1005:1012  "counter"
                let _3 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_19 := _3
                /// @src 0:1015:1016  "1"
                let expr_20 := 0x01
                /// @src 0:1005:1016  "counter + 1"
                let expr_21 := checked_add_t_uint256(expr_19, convert_t_rational_1_by_1_to_t_uint256(expr_20))

                /// @src 0:995:1016  "counter = counter + 1"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_21)
                let expr_22 := expr_21
                /// @src 0:1042:1043  "x"
                let _4 := var_x_9
                let expr_26 := _4
                /// @src 0:1027:1043  "uint256 varA = x"
                let var_varA_25 := expr_26
                /// @src 0:1068:1069  "y"
                let _5 := var_y_11
                let expr_30 := _5
                /// @src 0:1053:1069  "uint256 varB = y"
                let var_varB_29 := expr_30
                /// @src 0:1127:1131  "varA"
                let _6 := var_varA_25
                let expr_34 := _6
                /// @src 0:1113:1131  "uint256 tmp = varA"
                let var_tmp_33 := expr_34
                /// @src 0:1222:1226  "true"
                let expr_37 := 0x01
                /// @src 0:1215:1226  "flag = true"
                update_storage_value_offset_0t_bool_to_t_bool(0x01, expr_37)
                let expr_38 := expr_37
                /// @src 0:1277:1281  "varB"
                let _7 := var_varB_29
                let expr_41 := _7
                /// @src 0:1270:1281  "varA = varB"
                var_varA_25 := expr_41
                let expr_42 := expr_41
                /// @src 0:1371:1378  "counter"
                let _8 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_45 := _8
                /// @src 0:1365:1378  "log = counter"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x02, expr_45)
                let expr_46 := expr_45
                /// @src 0:1429:1432  "tmp"
                let _9 := var_tmp_33
                let expr_49 := _9
                /// @src 0:1422:1432  "varB = tmp"
                var_varB_29 := expr_49
                let expr_50 := expr_49
                /// @src 0:1507:1514  "counter"
                let _10 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_53 := _10
                /// @src 0:1517:1518  "1"
                let expr_54 := 0x01
                /// @src 0:1507:1518  "counter + 1"
                let expr_55 := checked_add_t_uint256(expr_53, convert_t_rational_1_by_1_to_t_uint256(expr_54))

                /// @src 0:1497:1518  "counter = counter + 1"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_55)
                let expr_56 := expr_55
                /// @src 0:1537:1541  "varA"
                let _11 := var_varA_25
                let expr_58 := _11
                /// @src 0:1536:1548  "(varA, varB)"
                let expr_60_component_1 := expr_58
                /// @src 0:1543:1547  "varB"
                let _12 := var_varB_29
                let expr_59 := _12
                /// @src 0:1536:1548  "(varA, varB)"
                let expr_60_component_2 := expr_59
                /// @src 0:1529:1548  "return (varA, varB)"
                var__14 := expr_60_component_1
                var__16 := expr_60_component_2
                leave

            }
            /// @src 0:685:1557  "contract A {..."

        }

        data ".metadata" hex"a26469706673582212204412395191e3f0119eec23ed028397a1d4b5c0bda8e1274e04f6ce78540fe4ec64736f6c634300081a0033"
    }

}


