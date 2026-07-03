IR:

/// @use-src 0:"Ao.sol"
object "A_42" {
    code {
        /// @src 0:190:647  "contract A {..."
        mstore(64, memoryguard(128))
        if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }

        constructor_A_42()

        let _1 := allocate_unbounded()
        codecopy(_1, dataoffset("A_42_deployed"), datasize("A_42_deployed"))

        return(_1, datasize("A_42_deployed"))

        function allocate_unbounded() -> memPtr {
            memPtr := mload(64)
        }

        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() {
            revert(0, 0)
        }

        /// @src 0:190:647  "contract A {..."
        function constructor_A_42() {

            /// @src 0:190:647  "contract A {..."

        }
        /// @src 0:190:647  "contract A {..."

    }
    /// @use-src 0:"Ao.sol"
    object "A_42_deployed" {
        code {
            /// @src 0:190:647  "contract A {..."
            mstore(64, memoryguard(128))

            if iszero(lt(calldatasize(), 4))
            {
                let selector := shift_right_224_unsigned(calldataload(0))
                switch selector

                case 0x2113522a
                {
                    // lastCaller()

                    external_fun_lastCaller_5()
                }

                case 0x27e235e3
                {
                    // balances(address)

                    external_fun_balances_9()
                }

                case 0x724658c1
                {
                    // f(address,uint256)

                    external_fun_f_41()
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

            function abi_decode_tuple_(headStart, dataEnd)   {
                if slt(sub(dataEnd, headStart), 0) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

            }

            function shift_right_unsigned_dynamic(bits, value) -> newValue {
                newValue :=

                shr(bits, value)

            }

            function cleanup_from_storage_t_address(value) -> cleaned {
                cleaned := and(value, 0xffffffffffffffffffffffffffffffffffffffff)
            }

            function extract_from_storage_value_dynamict_address(slot_value, offset) -> value {
                value := cleanup_from_storage_t_address(shift_right_unsigned_dynamic(mul(offset, 8), slot_value))
            }

            function read_from_storage_split_dynamic_t_address(slot, offset) -> value {
                value := extract_from_storage_value_dynamict_address(sload(slot), offset)

            }

            /// @ast-id 5
            /// @src 0:223:248  "address public lastCaller"
            function getter_fun_lastCaller_5() -> ret {

                let slot := 0
                let offset := 0

                ret := read_from_storage_split_dynamic_t_address(slot, offset)

            }
            /// @src 0:190:647  "contract A {..."

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

            function external_fun_lastCaller_5() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                abi_decode_tuple_(4, calldatasize())
                let ret_0 :=  getter_fun_lastCaller_5()
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_address__to_t_address__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_c1322bf8034eace5e0b5c7295db60986aa89aae5e0ea0873e4689e076861a5db() {
                revert(0, 0)
            }

            function validator_revert_t_address(value) {
                if iszero(eq(value, cleanup_t_address(value))) { revert(0, 0) }
            }

            function abi_decode_t_address(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_address(value)
            }

            function abi_decode_tuple_t_address(headStart, dataEnd) -> value0 {
                if slt(sub(dataEnd, headStart), 32) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_address(add(headStart, offset), dataEnd)
                }

            }

            function identity(value) -> ret {
                ret := value
            }

            function convert_t_uint160_to_t_uint160(value) -> converted {
                converted := cleanup_t_uint160(identity(cleanup_t_uint160(value)))
            }

            function convert_t_uint160_to_t_address(value) -> converted {
                converted := convert_t_uint160_to_t_uint160(value)
            }

            function convert_t_address_to_t_address(value) -> converted {
                converted := convert_t_uint160_to_t_address(value)
            }

            function mapping_index_access_t_mapping$_t_address_$_t_uint256_$_of_t_address(slot , key) -> dataSlot {
                mstore(0, convert_t_address_to_t_address(key))
                mstore(0x20, slot)
                dataSlot := keccak256(0, 0x40)
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

            /// @ast-id 9
            /// @src 0:254:297  "mapping(address => uint256) public balances"
            function getter_fun_balances_9(key_0) -> ret {

                let slot := 1
                let offset := 0

                slot := mapping_index_access_t_mapping$_t_address_$_t_uint256_$_of_t_address(slot, key_0)

                ret := read_from_storage_split_dynamic_t_uint256(slot, offset)

            }
            /// @src 0:190:647  "contract A {..."

            function cleanup_t_uint256(value) -> cleaned {
                cleaned := value
            }

            function abi_encode_t_uint256_to_t_uint256_fromStack(value, pos) {
                mstore(pos, cleanup_t_uint256(value))
            }

            function abi_encode_tuple_t_uint256__to_t_uint256__fromStack(headStart , value0) -> tail {
                tail := add(headStart, 32)

                abi_encode_t_uint256_to_t_uint256_fromStack(value0,  add(headStart, 0))

            }

            function external_fun_balances_9() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0 :=  abi_decode_tuple_t_address(4, calldatasize())
                let ret_0 :=  getter_fun_balances_9(param_0)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple_t_uint256__to_t_uint256__fromStack(memPos , ret_0)
                return(memPos, sub(memEnd, memPos))

            }

            function validator_revert_t_uint256(value) {
                if iszero(eq(value, cleanup_t_uint256(value))) { revert(0, 0) }
            }

            function abi_decode_t_uint256(offset, end) -> value {
                value := calldataload(offset)
                validator_revert_t_uint256(value)
            }

            function abi_decode_tuple_t_addresst_uint256(headStart, dataEnd) -> value0, value1 {
                if slt(sub(dataEnd, headStart), 64) { revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b() }

                {

                    let offset := 0

                    value0 := abi_decode_t_address(add(headStart, offset), dataEnd)
                }

                {

                    let offset := 32

                    value1 := abi_decode_t_uint256(add(headStart, offset), dataEnd)
                }

            }

            function abi_encode_tuple__to__fromStack(headStart ) -> tail {
                tail := add(headStart, 0)

            }

            function external_fun_f_41() {

                if callvalue() { revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb() }
                let param_0, param_1 :=  abi_decode_tuple_t_addresst_uint256(4, calldatasize())
                fun_f_41(param_0, param_1)
                let memPos := allocate_unbounded()
                let memEnd := abi_encode_tuple__to__fromStack(memPos  )
                return(memPos, sub(memEnd, memPos))

            }

            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74() {
                revert(0, 0)
            }

            function shift_left_0(value) -> newValue {
                newValue :=

                shl(0, value)

            }

            function update_byte_slice_20_shift_0(value, toInsert) -> result {
                let mask := 0xffffffffffffffffffffffffffffffffffffffff
                toInsert := shift_left_0(toInsert)
                value := and(value, not(mask))
                result := or(value, and(toInsert, mask))
            }

            function prepare_store_t_address(value) -> ret {
                ret := value
            }

            function update_storage_value_offset_0t_address_to_t_address(slot, value_0) {
                let convertedValue_0 := convert_t_address_to_t_address(value_0)
                sstore(slot, update_byte_slice_20_shift_0(sload(slot), prepare_store_t_address(convertedValue_0)))
            }

            function cleanup_t_rational_0_by_1(value) -> cleaned {
                cleaned := value
            }

            function convert_t_rational_0_by_1_to_t_uint160(value) -> converted {
                converted := cleanup_t_uint160(identity(cleanup_t_rational_0_by_1(value)))
            }

            function convert_t_rational_0_by_1_to_t_address(value) -> converted {
                converted := convert_t_rational_0_by_1_to_t_uint160(value)
            }

            function cleanup_t_bool(value) -> cleaned {
                cleaned := iszero(iszero(value))
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

            /// @ast-id 41
            /// @src 0:304:645  "function f(address to, uint256 amount) external {..."
            function fun_f_41(var_to_11, var_amount_13) {

                /// @src 0:418:428  "msg.sender"
                let expr_18 := caller()
                /// @src 0:405:428  "lastCaller = msg.sender"
                update_storage_value_offset_0t_address_to_t_address(0x00, expr_18)
                let expr_19 := expr_18
                /// @src 0:511:513  "to"
                let _1 := var_to_11
                let expr_21 := _1
                /// @src 0:525:526  "0"
                let expr_24 := 0x00
                /// @src 0:517:527  "address(0)"
                let expr_25 := convert_t_rational_0_by_1_to_t_address(expr_24)
                /// @src 0:511:527  "to != address(0)"
                let expr_26 := iszero(eq(cleanup_t_address(expr_21), cleanup_t_address(expr_25)))
                /// @src 0:510:528  "(to != address(0))"
                let expr_27 := expr_26
                /// @src 0:509:528  "!(to != address(0))"
                let expr_28 := cleanup_t_bool(iszero(expr_27))
                /// @src 0:505:565  "if (!(to != address(0))) {..."
                if expr_28 {
                    /// @src 0:551:554  "E()"
                    {

                        let _3 := 0

                        mstore(_3, 0x92bbf6e800000000000000000000000000000000000000000000000000000000)
                        let _2 := abi_encode_tuple__to__fromStack(add(_3, 4) )
                        revert(_3, sub(_2, _3))
                    }/// @src 0:505:565  "if (!(to != address(0))) {..."
                }
                /// @src 0:632:638  "amount"
                let _4 := var_amount_13
                let expr_37 := _4
                /// @src 0:617:625  "balances"
                let _5_slot := 0x01
                let expr_34_slot := _5_slot
                /// @src 0:626:628  "to"
                let _6 := var_to_11
                let expr_35 := _6
                /// @src 0:617:629  "balances[to]"
                let _7 := mapping_index_access_t_mapping$_t_address_$_t_uint256_$_of_t_address(expr_34_slot,expr_35)
                /// @src 0:617:638  "balances[to] = amount"
                update_storage_value_offset_0t_uint256_to_t_uint256(_7, expr_37)
                let expr_38 := expr_37

            }
            /// @src 0:190:647  "contract A {..."

        }

        data ".metadata" hex"a2646970667358221220afa368a54a6e38bf1ed4ebfa9c80e0321f14c9054eb477369e1beaadfae53a2e64736f6c634300081a0033"
    }

}


