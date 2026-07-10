// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// Rule 0.1 — LEFT side: temporary-based swap with P and Q INTERLEAVED.
//
//   R
//   tmp = varA        <-- swap step 1
//   P                 <-- interleaved block P (must NOT read/write varA, varB, tmp)
//   varA = varB       <-- swap step 2
//   Q                 <-- interleaved block Q (must NOT read/write varA, varB, tmp)
//   varB = tmp        <-- swap step 3
//   S
//
// PROVISO (Rule 0.1): tmp, varA, varB (and the compiler temporary c on the other
// side) do not occur in P or Q.  Here P and Q touch ONLY unrelated state
// (`counter`, `flag`, `log`) — never varA/varB/tmp — so the transformation is sound.
contract A {
    // unrelated state that P and Q may touch (does NOT alias the swap variables)
    uint256 public counter;
    bool     public flag;
    uint256 public log;

    function f(uint256 x, uint256 y) external returns (uint256, uint256) {
        // R : prelude (does not read the swap vars)
        counter = counter + 1;

        uint256 varA = x;
        uint256 varB = y;

        // ---- swap step 1 ----
        uint256 tmp = varA;

        // ---- P (interleaved) : reads/writes only unrelated state ----
        flag = true;

        // ---- swap step 2 ----
        varA = varB;

        // ---- Q (interleaved) : reads/writes only unrelated state ----
        log = counter;

        // ---- swap step 3 ----
        varB = tmp;

        // S : epilogue (does not read the swap vars)
        counter = counter + 1;

        return (varA, varB);
    }
}