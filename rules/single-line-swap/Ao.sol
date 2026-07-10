// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Rule 0.1 — RIGHT side: simultaneous swap up front, then P and Q consecutively.
//
//   R
//   (varA, varB) = (varB, varA)   <-- atomic swap (compiler introduces temporary c)
//   P                             <-- same P as on the left
//   Q                             <-- same Q as on the left
//   S
//
// Same P, Q, S as A.sol; they touch only unrelated state, so the proviso holds
// and this program is observationally equivalent to A.sol under Rule 0.1.
contract Ao {
    uint256 public counter;
    bool     public flag;
    uint256 public log;

    function f(uint256 x, uint256 y) external returns (uint256, uint256) {
        // R : prelude
        counter = counter + 1;

        uint256 varA = x;
        uint256 varB = y;

        // ---- atomic simultaneous swap ----
        (varA, varB) = (varB, varA);

        // ---- P (now consecutive, unchanged) ----
        flag = true;

        // ---- Q (now consecutive, unchanged) ----
        log = counter;

        // S : epilogue
        counter = counter + 1;

        return (varA, varB);
    }
}