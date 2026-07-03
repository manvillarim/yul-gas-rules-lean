# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Overview

A formal model of the EVM and Yul in Lean 4, using Lean's `autoImplicit=false` project-wide. The EVM primops are shared by and reused in the Yul semantics. Depends on Mathlib (`v4.22.0`) and Lean `v4.22.0`.

## Commands

```bash
# Build the project
lake build

# Run EVM conformance tests (BlockchainTests submodule)
lake test -- <NUM_THREADS> 2> out_discard.txt

# Run Yul semantics tests
lake exe yulSemanticsTests
```

The `EthereumTests/` git submodule is automatically initialized on first build via the `extern_lib libleanffi` target in `lakefile.lean`. The FFI layer also clones `sha-2` and `SHA3IUF` C libraries into the build directory on first build.

## Architecture

### Shared primitives

- **`EvmYul/Operations.lean`** — `Operation τ` ADT parameterized by `OperationType` (`.EVM` or `.Yul`). Covers all opcodes across arithmetic, memory, storage, control flow, etc.
- **`EvmYul/UInt256.lean`** — 256-bit word type used throughout.
- **`EvmYul/MachineState.lean`** — `MachineState` (gas, memory, return data).
- **`EvmYul/State.lean`** — `State τ` (account map, substate, execution env, block headers). The `τ : OperationType` parameter threads through nearly everything.
- **`EvmYul/SharedState.lean`** — `SharedState τ` extends both `State τ` and `MachineState`.

### EVM model (`EvmYul/EVM/`)

| File | Purpose |
|---|---|
| `State.lean` | `EVM.State` extends `SharedState .EVM`, adds `pc`, `stack`, `execLength` |
| `Semantics.lean` | `step` function — single EVM instruction execution |
| `PrimOps.lean` | EVM primop implementations |
| `Gas.lean` / `GasConstants.lean` | Gas accounting |
| `PrecompiledContracts.lean` | Precompile dispatch |
| `Instr.lean` | Instruction decoding |

### Yul model (`EvmYul/Yul/`)

| File | Purpose |
|---|---|
| `Ast.lean` | `Stmt`, `Expr`, `FunctionDefinition` mutual inductive; `YulContract` |
| `State.lean` | `Yul.State` — `Ok (SharedState .Yul) VarStore \| OutOfFuel \| Checkpoint Jump` |
| `Interpreter.lean` | `exec`/`eval` mutual recursion — main Yul semantics |
| `PrimOps.lean` | `primCall` — dispatches `Operation .Yul` to state transformers |
| `YulNotation.lean` | Lean macro syntax (`<s { ... }>`, `<f function ... >`) for writing Yul inline |
| `YulSemanticsTests/Main.lean` | Integration tests with concrete Yul contracts |
| `Execmono.lean` | Scaffold for fuel-monotonicity proof (contains `sorry`s, not sound) |

### Conformance testing (`Conform/`)

Runs Ethereum `BlockchainTests` JSON tests from the `EthereumTests/` submodule. Entry point is `Conform/Main.lean`; test parsing is in `Conform/TestParser.lean`. Tests run in parallel across N threads.

### FFI (`EvmYul/FFI/`)

C implementations of SHA-256, Keccak-256, BLAKE2 are linked as a static library `libleanffi`. Lean-side bindings in `FFI/ffi.lean` expose `@[extern]` opaques.

## Key design notes

- The `OperationType` parameter (`.EVM` / `.Yul`) is used to specialize `State`, `SharedState`, `Operation`, `ExecutionEnv`, and `AccountMap`. It lets the same structures serve both interpreters while keeping their types distinct.
- Yul `State` is an inductive (not a structure) to represent `OutOfFuel` and `Checkpoint` control-flow cases alongside the normal `Ok` case.
- The Yul interpreter uses a fuel/heartbeat limit (`maxHeartbeats 400000` in `Interpreter.lean`).
- Gas is not modelled in Yul semantics. `create`/`create2`, `EXTCODESIZE`, `EXTCODEHASH`, `EXTCODECOPY`, `CODECOPY`, `CODESIZE` are unmodelled and return `default`.
- `autoImplicit=false` is enforced globally; a few files locally re-enable it with `set_option autoImplicit true`.
