// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Lado "require" da Law1.
//   P ; require(B, M) ; Q
// com B = (to != address(0)), M = "zero address".
contract A {
    address public lastCaller;
    mapping(address => uint256) public balances;

    function f(address to, uint256 amount) external {
        // P : statements before the check
        lastCaller = msg.sender;

        // the check
        require(to != address(0), "zero address");

        // Q : statements after the check
        balances[to] = amount;
    }
}
