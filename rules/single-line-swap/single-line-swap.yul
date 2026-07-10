IR:

/// @use-src 0:"Ao.sol"
object "Ao_60" {
    code {
        /// @src 0:524:1126  "contract Ao {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_Ao_60()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("Ao_60_deployed"), datasize("Ao_60_deployed"))

        return(_1, datasize("Ao_60_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:524:1126  "contract Ao {..."
        function constructor_Ao_60() {

            /// @src 0:524:1126  "contract Ao {..."

        }
        /// @src 0:524:1126  "contract Ao {..."

    }
    /// @use-src 0:"Ao.sol"
    object "Ao_60_deployed" {
        code {
            /// @src 0:524:1126  "contract Ao {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x13d1aa2e
                {
                    // f(uint256,uint256)

                    external_fun_f_59()
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

            function external_fun_f_59() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_uint256t_uint256(4, calldatasize())
                let ret_0, ret_1 :=  fun_f_59(param_0, param_1)
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
            /// @src 0:596:614  "uint256 public log"
            function getter_fun_log_7() -> ret {

                let slot := 2
                let offset := 0

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:524:1126  "contract Ao {..."

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
            /// @src 0:542:564  "uint256 public counter"
            function getter_fun_counter_3() -> ret {

                let slot := 0
                let offset := 0

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:524:1126  "contract Ao {..."

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
            /// @src 0:570:590  "bool     public flag"
            function getter_fun_flag_5() -> ret {

                let slot := 1
                let offset := 0

                ret := read_from_storage_split_dynamic_t_bool(slot, offset)

            }
            /// @src 0:524:1126  "contract Ao {..."

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

            /// @ast-id 59
            /// @src 0:621:1124  "function f(uint256 x, uint256 y) external returns (uint256, uint256) {..."
            function fun_f_59(var_x_9, var_y_11) -> var__14, var__16 {
                /// @src 0:672:679  "uint256"
                let zero_t_uint256_1 := zero_value_for_split_t_uint256()
                var__14 := zero_t_uint256_1
                /// @src 0:681:688  "uint256"
                let zero_t_uint256_2 := zero_value_for_split_t_uint256()
                var__16 := zero_t_uint256_2

                /// @src 0:733:740  "counter"
                let _3 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_19 := _3
                /// @src 0:743:744  "1"
                let expr_20 := 0x01
                /// @src 0:733:744  "counter + 1"
                let expr_21 := checked_add_t_uint256(expr_19, convert_t_rational_1_by_1_to_t_uint256(expr_20))

                /// @src 0:723:744  "counter = counter + 1"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_21)
                let expr_22 := expr_21
                /// @src 0:770:771  "x"
                let _4 := var_x_9
                let expr_26 := _4
                /// @src 0:755:771  "uint256 varA = x"
                let var_varA_25 := expr_26
                /// @src 0:796:797  "y"
                let _5 := var_y_11
                let expr_30 := _5
                /// @src 0:781:797  "uint256 varB = y"
                let var_varB_29 := expr_30
                /// @src 0:870:874  "varB"
                let _6 := var_varB_29
                let expr_35 := _6
                /// @src 0:869:881  "(varB, varA)"
                let expr_37_component_1 := expr_35
                /// @src 0:876:880  "varA"
                let _7 := var_varA_25
                let expr_36 := _7
                /// @src 0:869:881  "(varB, varA)"
                let expr_37_component_2 := expr_36
                /// @src 0:854:881  "(varA, varB) = (varB, varA)"
                var_varB_29 := expr_37_component_2
                var_varA_25 := expr_37_component_1
                /// @src 0:951:955  "true"
                let expr_41 := 0x01
                /// @src 0:944:955  "flag = true"
                update_storage_value_offset_0t_bool_to_t_bool(0x01, expr_41)
                let expr_42 := expr_41
                /// @src 0:1024:1031  "counter"
                let _8 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_45 := _8
                /// @src 0:1018:1031  "log = counter"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x02, expr_45)
                let expr_46 := expr_45
                /// @src 0:1076:1083  "counter"
                let _9 := read_from_storage_split_offset_0_t_uint256(0x00)
                let expr_49 := _9
                /// @src 0:1086:1087  "1"
                let expr_50 := 0x01
                /// @src 0:1076:1087  "counter + 1"
                let expr_51 := checked_add_t_uint256(expr_49, convert_t_rational_1_by_1_to_t_uint256(expr_50))

                /// @src 0:1066:1087  "counter = counter + 1"
                update_storage_value_offset_0t_uint256_to_t_uint256(0x00, expr_51)
                let expr_52 := expr_51
                /// @src 0:1106:1110  "varA"
                let _10 := var_varA_25
                let expr_54 := _10
                /// @src 0:1105:1117  "(varA, varB)"
                let expr_56_component_1 := expr_54
                /// @src 0:1112:1116  "varB"
                let _11 := var_varB_29
                let expr_55 := _11
                /// @src 0:1105:1117  "(varA, varB)"
                let expr_56_component_2 := expr_55
                /// @src 0:1098:1117  "return (varA, varB)"
                var__14 := expr_56_component_1
                var__16 := expr_56_component_2
                leave

            }
            /// @src 0:524:1126  "contract Ao {..."

        }

        data ".metadata" hex"a26469706673582212207a7f962d56260093c8815f6a05ae7d0406e09ebaac36e300a928eadf086f62a664736f6c634300081a0033"
    }

}


