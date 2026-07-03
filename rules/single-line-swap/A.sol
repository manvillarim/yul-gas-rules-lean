// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// P ; tmp = varA ; varA = varB ; varB = tmp ; Q
contract A {
    address public lastCaller;
    uint256 public total;

    function f(uint256 x, uint256 y) external returns (uint256, uint256) {
        // P : statements before the swap
        lastCaller = msg.sender;

        uint256 varA = x;
        uint256 varB = y;

        // the swap (temp form) 
        uint256 tmp = varA;
        varA = varB;
        varB = tmp;

        // Q : statements after the FULL swap 
        total = varA + varB;

        return (varA, varB);
    }
}