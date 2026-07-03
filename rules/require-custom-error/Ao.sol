// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Lado "custom error" da Law1.
//   P ; if (!B) { revert E(); } ; Q
// mesmo B = (to != address(0)); a mensagem M vira o erro E().
contract A {
    error E();

    address public lastCaller;
    mapping(address => uint256) public balances;

    function f(address to, uint256 amount) external {
        // P : statements before the check
        lastCaller = msg.sender;

        // the check (custom-error form, negacao literal da Law1)
        if (!(to != address(0))) {
            revert E();
        }

        // Q : statements after the check
        balances[to] = amount;
    }
}
