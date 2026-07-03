// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// P ; (varA, varB) = (varB, varA) ; Q
contract Ao {
    address public lastCaller;
    uint256 public total;

    function f(uint256 x, uint256 y) external returns (uint256, uint256) {
        // P : statements before the swap
        lastCaller = msg.sender;

        uint256 varA = x;
        uint256 varB = y;

        // the swap (simultaneous-assignment form)
        (varA, varB) = (varB, varA);

        // Q : statements after the swap
        total = varA + varB;

        return (varA, varB);
    }
}