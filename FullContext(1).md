Project Path: EVMYulLean

Source Tree:

```txt
EVMYulLean
├── Conform
│   ├── Exception.lean
│   ├── Main.lean
│   ├── Model.lean
│   ├── TestParser.lean
│   ├── TestRunner.lean
│   └── Wheels.lean
├── EthereumTests
├── EvmYul
│   ├── BLAKE2_F.lean
│   ├── BN_ADD.lean
│   ├── BN_MUL.lean
│   ├── Data
│   │   └── Stack.lean
│   ├── EVM
│   │   ├── Exception.lean
│   │   ├── Gas.lean
│   │   ├── GasConstants.lean
│   │   ├── Instr.lean
│   │   ├── PrecompiledContracts.lean
│   │   ├── PrimOps.lean
│   │   ├── Semantics.lean
│   │   ├── State.lean
│   │   └── StateOps.lean
│   ├── EllipticCurves.lean
│   ├── EllipticCurvesPy
│   │   ├── __init__.py
│   │   ├── alt_bn128.py
│   │   ├── base_types.py
│   │   ├── blake2.py
│   │   ├── blake2_f.py
│   │   ├── bn_add.py
│   │   ├── bn_mul.py
│   │   ├── elliptic_curve.py
│   │   ├── exceptions.py
│   │   ├── finite_field.py
│   │   ├── hash.py
│   │   ├── keccak.py
│   │   ├── kzg.py
│   │   ├── point_evaluation.py
│   │   ├── previous_trie.py
│   │   ├── recover.py
│   │   ├── rip160.py
│   │   ├── rlp.py
│   │   ├── sha256.py
│   │   ├── sign.py
│   │   ├── snarkv.py
│   │   ├── trie.py
│   │   └── trie_root.py
│   ├── FFI
│   │   ├── ffi.c
│   │   └── ffi.lean
│   ├── MachineState.lean
│   ├── MachineStateOps.lean
│   ├── Maps
│   │   ├── AccountMap.lean
│   │   ├── ByteMap.lean
│   │   └── StorageMap.lean
│   ├── Operations.lean
│   ├── PerformIO.lean
│   ├── PointEval.lean
│   ├── Pretty.lean
│   ├── RIP160.lean
│   ├── SHA256.lean
│   ├── SNARKV.lean
│   ├── Semantics.lean
│   ├── SharedState.lean
│   ├── SharedStateOps.lean
│   ├── SpongeHash
│   │   └── Keccak256.lean
│   ├── State
│   │   ├── Account.lean
│   │   ├── AccountOps.lean
│   │   ├── Block.lean
│   │   ├── BlockHeader.lean
│   │   ├── ExecutionEnv.lean
│   │   ├── Substate.lean
│   │   ├── SubstateOps.lean
│   │   ├── Transaction.lean
│   │   ├── TransactionOps.lean
│   │   ├── TrieRoot.lean
│   │   └── Withdrawal.lean
│   ├── State.lean
│   ├── StateOps.lean
│   ├── UInt256.lean
│   ├── Wheels.lean
│   └── Yul
│       ├── Ast.lean
│       ├── Exception.lean
│       ├── Interpreter.lean
│       ├── MachineState.lean
│       ├── PrimOps.lean
│       ├── SizeLemmas.lean
│       ├── State.lean
│       ├── StateOps.lean
│       ├── Wheels.lean
│       ├── YulNotation.lean
│       └── YulSemanticsTests
│           ├── Caller.sol
│           ├── Caller.yul
│           ├── Caller2.sol
│           ├── Caller2.yul
│           ├── Main.lean
│           ├── README.md
│           ├── Storage.sol
│           ├── Storage.yul
│           ├── Storage2.sol
│           ├── Storage2.yul
│           └── shell.nix
├── EvmYul.lean
├── README.md
├── SpongeHash.lean
├── lake-manifest.json
├── lakefile.lean
├── lean-toolchain
├── license.txt
├── openssl.cnf
└── shell.nix

```

`Conform/Exception.lean`:

```lean
import EvmYul.EVM.Exception

namespace EvmYul

namespace Conform

/--
`Exception` represents the class of conformance testing errors.
- `CannotParse`          - The `Json` of a test is malformed. `why` is the reason. 
- `InvalidTestStructure` - The structure of tests has been violated. `why` is the reason. 
-/
inductive Exception where
  | CannotParse (why : String)
  | InvalidTestStructure (why : String)
  deriving Repr

end Conform

end EvmYul

```
`Conform/Main.lean`:

```lean
import Conform.TestRunner
import EvmYul.FFI.ffi

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

private def basicSuccess (name : System.FilePath)
                         (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Batteries.RBMap String EvmYul.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keys, failed.keys)

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open EvmYul.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open EvmYul.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false) : IO (Nat × Array String) := do
  let isToBeTested (testname : String) : Bool :=
    let whitelist := testWhitelist
    let blacklist := testBlacklist ++ EvmYul.Conform.GlobalBlacklist
    testname ∉ blacklist ∧ (whitelist.isEmpty ∨ testname ∈ whitelist)

  let testFiles ←
    Array.filter isTestFile <$>
      System.FilePath.walkDir root (pure <| · ∉ directoryBlacklist)

  let testFiles := testFiles.filter (· ∉ fileBlacklist)

  let mut discardedFiles : Array EvmYul.Conform.TestId := #[]
  let mut numSuccess := 0

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  let testJsons ← testFiles.mapM Lean.Json.fromFile
  let testNames : Array (System.FilePath × Array String) :=
    testJsons.zip testFiles |>.map
      λ (json, filepath) ↦
        match json.getObj? with
        | .error _ => panic! "Malformed test json."
        | .ok x => (filepath, x.toArray.map Sigma.fst |>.filter isToBeTested)  

  let mut tasks : Array (Task _) := .empty
  let mut thread := 0
  let mut tests : Array (Array (System.FilePath × String)) := .replicate threads #[]

  IO.println s!"Scheduling tests for parallel execution..."
  for (path, names) in testNames do
    for name in names do
      tests := tests.set! thread (tests[thread]! |>.push (path, name))
      thread := thread + 1; thread := thread % threads
  for i in [0:threads] do
    tasks := tasks.push (←IO.asTask <| EvmYul.Conform.processTests tests[i]! (if timed then .some i else .none))

  let mut failedTests : Array String := .empty

  IO.println s!"Scheduled {tests.foldl (· + ·.size) 0} tests on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res) in batch do
      log file test res phase
      if res.isNone
      then numSuccess := numSuccess + 1
      else failedTests := failedTests.push test
  return (numSuccess, failedTests)

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trim.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let ExpectedToFail : Std.HashSet String := {
    "invalid_block_blob_count.json[src/GeneralStateTestsFiller/Pyspecs/cancun/eip4844_blobs/test_blob_txs.py::test_invalid_block_blob_count[fork_Cancun-blockchain_test--blobs_per_tx_(7,)]]",
    "GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast.json[GasUsedHigherThanBlockGasLimitButNotWithRefundsSuicideLast_Cancun]"
  }

  let DelayFiles : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun",
      "SuicideIssue_Cancun"]

  let printResults (result : ℕ × Array String) : IO (Array String) := do
    let (success, failure) := result
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
    IO.println s!"Succeeded: {success}"
    IO.println s!"Success rate of: {(success.toFloat / (failure.size + success).toFloat) * 100.0}"
    IO.println s!"Failed tests:\n{failure}"
    return failure

  IO.println s!"Phase 1/3 - No performance tests."
  let failed₁ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
                          (testBlacklist := DelayFiles)
                          (phase := 1)
                          (threads := NumThreads) >>= printResults
  
  IO.println s!"Phase 2/3 - Performance tests only."
  let failed₂ ← testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
                          (phase := 2)
                          (threads := NumThreads) >>= printResults


  IO.println s!"Phase 3/3 - Individually scheduled tests."
  let failed₃ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testWhitelist := DelayFiles)
                          (phase := 3)
                          (threads := NumThreads) >>= printResults

  return if (Std.HashSet.ofArray (failed₁ ++ failed₂ ++ failed₃) |>.diff ExpectedToFail).isEmpty then 0 else 1

```
`Conform/Model.lean`:

```lean
import Lean.Data.RBMap
import Lean.Data.Json

-- import EvmYul.Maps
import EvmYul.Operations
import EvmYul.Wheels
import EvmYul.State.Withdrawal
import EvmYul.State.Block

import EvmYul.EVM.State

import Conform.Wheels

namespace EvmYul

namespace Conform

section Model

open Lean

def AddrMap.keys {α : Type} [Inhabited α] (self : AddrMap α) : Multiset AccountAddress :=
  .ofList <| self.toList.map Prod.fst

instance : LE ((_ : UInt256) × UInt256) where
  le lhs rhs := if lhs.1.val = rhs.1.val then lhs.2.val ≤ rhs.2.val else lhs.1.val ≤ rhs.1.val

instance : IsTrans ((_ : UInt256) × UInt256) (· ≤ ·) where
  trans a b c h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    rcases c with ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
    unfold LE.le instLESigmaUInt256_conform at h₁ h₂ ⊢; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsAntisymm ((_ : UInt256) × UInt256) (· ≤ ·) where
  antisymm a b h₁ h₂ := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform at h₁ h₂; simp at *
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : IsTotal ((_ : UInt256) × UInt256) (· ≤ ·) where
  total a b := by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform; simp
    aesop (config := {warnOnNonterminal := false}) <;> omega

instance : DecidableRel (α := (_ : UInt256) × UInt256) (· ≤ ·) :=
  λ a b ↦ by
    rcases a with ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    rcases b with ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩
    unfold LE.le instLESigmaUInt256_conform; simp
    aesop (config := {warnOnNonterminal := false}) <;> exact inferInstance

abbrev Code := ByteArray

abbrev Pre := PersistentAccountMap .EVM

abbrev PostEntry := PersistentAccountState .EVM

abbrev Post := PersistentAccountMap .EVM

abbrev Transactions := Array Transaction

abbrev Withdrawals := Array Withdrawal

private local instance : Repr Json := ⟨λ s _ ↦ Json.pretty s⟩

/--
In theory, parts of the TestEntry could deserialise immediately into the underlying `EVM.State`.
-/

inductive PostState where
  | Hash : ByteArray → PostState
  | Map : Post → PostState
  deriving Inhabited

structure TestEntry where
  info               : Json := ""
  blocks             : RawBlocks
  genesisRLP         : ByteArray
  lastblockhash      : UInt256
  network            : String
  postState          : PostState
  pre                : Pre
  sealEngine         : Json := ""
  deriving Inhabited

abbrev TestMap := Batteries.RBMap String TestEntry compare

abbrev AccessListEntry := AccountAddress × Array UInt256

abbrev AccessList := Array AccessListEntry

def TestResult := Option String
  deriving Repr, Inhabited

namespace TestResult

def isSuccess (self : TestResult) : Bool := self matches none

def isFailure (self : TestResult) : Bool := !self.isSuccess

def mkFailed (reason : String := "") : TestResult := .some reason

def mkSuccess : TestResult := .none

def ofBool (success : Bool) (reason : String := "Semantics error.") : TestResult :=
  if success then mkSuccess else mkFailed reason

end TestResult

end Model

```
`Conform/TestParser.lean`:

```lean
import Lean.Data.Json

import EvmYul.Wheels
import EvmYul.Operations
import EvmYul.EVM.Semantics
import EvmYul.Wheels
import EvmYul.State.Withdrawal

import Conform.Model
import Conform.Wheels

namespace EvmYul

namespace Conform

namespace Parser

section FromJson

open Lean (FromJson Json)

private def fromBlobString {α} (f : Blob → Except String α) : FromJson α :=
  {
    fromJson? := λ json ↦ json.getStr? >>= (getBlob? · >>= f)
  }

instance : FromJson UInt256 := fromBlobString UInt256.fromBlob?
instance : FromJson ℕ := fromBlobString Nat.fromBlob?

instance : FromJson AccountAddress := fromBlobString AccountAddress.fromBlob?

instance : FromJson Storage where
  fromJson? json := json.getObjVals? UInt256 UInt256

instance : FromJson ByteArray := fromBlobString (ByteArray.ofBlob)

instance : FromJson (PersistentAccountState .EVM) where
  fromJson? json := do
    pure {
      balance := ← json.getObjValAs? UInt256 "balance"
      nonce   := ← json.getObjValAs? UInt256 "nonce"
      code    := ← json.getObjValAs? Code    "code"
      storage := ← json.getObjValAs? Storage "storage"
    }

instance : FromJson Pre where
  fromJson? json := json.getObjVals? AccountAddress (PersistentAccountState .EVM)

instance : FromJson Post where
  fromJson? json := json.getObjVals? AccountAddress PostEntry

instance : FromJson BlockHeader where
  fromJson? json := do
    try
      pure {
        parentHash            := ← json.getObjValAsD! UInt256        "parentHash"
        ommersHash            := ← json.getObjValAsD! UInt256        "uncleHash"
        beneficiary           := ← json.getObjValAsD! AccountAddress "coinbase"
        stateRoot             := ← json.getObjValAsD! UInt256        "stateRoot"
        transRoot             := ← json.getObjValAsD! ByteArray      "transactionsTrie"
        receiptRoot           := ← json.getObjValAsD! ByteArray      "receiptTrie"
        logsBloom             := ← json.getObjValAsD! ByteArray      "bloom"
        difficulty            := ← json.getObjValAsD! ℕ              "difficulty"
        number                := ← json.getObjValAsD! ℕ              "number"
        gasLimit              := ← json.getObjValAsD! ℕ              "gasLimit"
        gasUsed               := ← json.getObjValAsD! ℕ              "gasUsed"
        timestamp             := ← json.getObjValAsD! ℕ              "timestamp"
        extraData             := ← json.getObjValAsD! ByteArray      "extraData"
        nonce                 := 0 -- [deprecated] 0.
        baseFeePerGas         := ← json.getObjValAsD! ℕ              "baseFeePerGas"
        parentBeaconBlockRoot := ← json.getObjValAsD! ByteArray      "parentBeaconBlockRoot"
        prevRandao            := ← json.getObjValAsD! UInt256        "mixHash"
        withdrawalsRoot       := ← json.getObjValAsD! ByteArray      "withdrawalsRoot"
        blobGasUsed           := ← json.getObjValAsD! UInt64         "blobGasUsed"
        excessBlobGas         := ← json.getObjValAsD! UInt64         "excessBlobGas"
      }
    catch ε => dbg_trace s!"Cannot parse BlockHeader: {ε}\n json: {json}"
               default

instance : FromJson AccessListEntry where
  fromJson? json := do
    let address     := ← json.getObjValAs? AccountAddress "address"
    let storageKeys := ← json.getObjValAs? (Array UInt256) "storageKeys"
    pure (address, storageKeys)

instance : FromJson Withdrawal where
  fromJson? json := do
    pure {
      index          := ← json.getObjValAs? UInt64         "index"
      validatorIndex := ← json.getObjValAs? UInt64         "validatorIndex"
      address        := ← json.getObjValAs? AccountAddress "address"
      amount         := ← json.getObjValAs? UInt64         "amount"
    }

instance : FromJson Transaction where
  fromJson? json := do
    let baseTransaction : Transaction.Base := {
      nonce          := ← json.getObjValAsD! UInt256 "nonce"
      gasLimit       := ← json.getObjValAsD! UInt256 "gasLimit"
      recipient      := ← match json.getObjVal? "to" with
                          | .error _ => .ok .none
                          | .ok ok => do let str ← ok.getStr?
                                         if str.isEmpty then .ok .none else FromJson.fromJson? str
      value          := ← json.getObjValAsD! UInt256   "value"
      r              := ← json.getObjValAsD! ByteArray "r"
      s              := ← json.getObjValAsD! ByteArray "s"
      data           := ← json.getObjValAsD! ByteArray "data"
    }

    match json.getObjVal? "accessList" with
      | .error _ => do
        return .legacy ⟨baseTransaction, ⟨← json.getObjValAsD! UInt256 "gasPrice"⟩, ← json.getObjValAsD! UInt256 "v"⟩
      | .ok accessList => do
        -- Any other transaction now necessarily has an access list.
        let accessListTransaction : Transaction.WithAccessList :=
          {
            chainId    := ← json.getObjValAsD UInt256 "chainId" ⟨1⟩
            accessList := ← FromJson.fromJson? accessList
            yParity    := ← json.getObjValAsD! UInt256 "v"
          }
        match json.getObjVal? "gasPrice" with
          | .ok gasPrice => do
            return .access ⟨baseTransaction, accessListTransaction, ⟨← FromJson.fromJson? gasPrice⟩⟩
          | .error _ =>
            let dynamic : DynamicFeeTransaction :=
              ⟨ baseTransaction
              , accessListTransaction
              , ← json.getObjValAsD! UInt256 "maxFeePerGas"
              , ← json.getObjValAsD! UInt256 "maxPriorityFeePerGas"
              ⟩
            match json.getObjVal? "maxFeePerBlobGas" with
            | .error _ =>
              pure <| .dynamic dynamic
            | .ok maxFeePerBlobGas =>
              pure <|
                .blob
                  ⟨ dynamic
                  , ← FromJson.fromJson? maxFeePerBlobGas
                  , ← json.getObjValAsD! (List ByteArray) "blobVersionedHashes"
                  ⟩

/--
- Format₀: `EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/add.json`
- Format₁: `EthereumTests/BlockchainTests/GeneralStateTests/Pyspecs/cancun/eip4844_blobs/invalid_static_excess_blob_gas.json`
-/
private def blockOfJson (json : Json) : Except String RawBlock := do
  -- The exception, if exists, is always in the outermost object regardless of the `<Format>` (see this function's docs).
  let exception ← json.getObjValAsD! (Option String) "expectException"
  let rlp ← json.getObjValAsD! ByteArray "rlp"
  pure {
    rlp
    exception := exception.option [] (·.splitOn "|")
  }
  where
    tryParseBlocknumber (s : String) : Except String Nat :=
      s.toNat?.elim (.error "Cannot parse `blocknumber`.") .ok

instance : FromJson RawBlock := ⟨blockOfJson⟩

instance : FromJson TestEntry where
  fromJson? json := do
    let post : PostState ←
      match json.getObjVal? "postStateHash" with
        | .error _ =>
          .Map <$> json.getObjValAsD! (PersistentAccountMap .EVM) "postState"
        | .ok postStateHash =>
          .Hash <$> FromJson.fromJson? postStateHash
    pure {
      info               := ← json.getObjValAs? Json "info"
      blocks             := ← json.getObjValAs? RawBlocks "blocks"
      genesisRLP         := ← json.getObjValAs? ByteArray "genesisRLP"
      lastblockhash      := ← json.getObjValAs? UInt256 "lastblockhash"
      network            := ← json.getObjValAs? String "network"
      postState          := post
      pre                := ← json.getObjValAs? Pre "pre"
      sealEngine         := ← json.getObjValAs? Json "sealEngine"
    }

instance : FromJson TestMap where
  fromJson? json := json.getObjVals? String TestEntry

end FromJson

def testNamesOfTest (test : Lean.Json) : Except String (Array String) :=
  test.getObj? <&> (·.toArray.map Sigma.fst)

section PrettyPrinter

instance : ToString (PersistentAccountState .EVM) := ⟨ToString.toString ∘ repr⟩

instance : ToString Pre := ⟨ToString.toString ∘ repr⟩

instance : ToString PostEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Post := ⟨ToString.toString ∘ repr⟩

instance : ToString AccessListEntry := ⟨ToString.toString ∘ repr⟩

instance : ToString Transaction := ⟨λ _ ↦ "Some transaction."⟩

end PrettyPrinter

end Parser

end Conform

end EvmYul

```
`Conform/TestRunner.lean`:

```lean
import EvmYul.EVM.State
import EvmYul.EVM.Semantics
import EvmYul.EVM.Gas
import EvmYul.Wheels

import EvmYul.State.TransactionOps
import EvmYul.State.Withdrawal

import EvmYul.Maps.AccountMap

import EvmYul.Pretty
import EvmYul.Wheels

import Conform.Exception
import Conform.Model
import Conform.TestParser

namespace EvmYul

namespace Conform

def VerySlowTests : Array String := #[]

def GlobalBlacklist : Array String := VerySlowTests

abbrev TestId : Type := System.FilePath × String

def PersistentAccountMap.toAccountMap (self : PersistentAccountMap .EVM) : AccountMap .EVM :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account .EVM :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage.toEvmYulStorage
      }
    s.insert addr account

def PersistentAccountMap.toEVMState (self : PersistentAccountMap .EVM) : EVM.State :=
  self.foldl addAccount default
  where addAccount s addr acc :=
    let account : Account .EVM :=
      {
        tstorage := ∅
        nonce    := acc.nonce
        balance  := acc.balance
        code     := acc.code
        storage  := acc.storage.toEvmYulStorage
      }
    { s with toState := s.setAccount addr account }

def Pre.toEVMState : Pre → EVM.State := PersistentAccountMap.toEVMState

def TestMap.toTests (self : TestMap) : List (String × TestEntry) := self.toList

def Post.toEVMState : Post → EVM.State := PersistentAccountMap.toEVMState

local instance : Inhabited EVM.Transformer where
  default := λ _ ↦ default

private def compareWithEVMdefaults (s₁ s₂ : EvmYul.Storage) : Bool :=
  withDefault s₁ == withDefault s₂
  where
    withDefault (s : EvmYul.Storage) : EvmYul.Storage := if s.contains ⟨0⟩ then s else s.insert ⟨0⟩ ⟨0⟩

/--
TODO - This should be a generic map complement, but we are not trying to write a library here.

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageComplement (m₁ m₂ : PersistentAccountMap .EVM) : PersistentAccountMap .EVM := Id.run do
  let mut result : PersistentAccountMap .EVM := m₁
  for ⟨k₂, v₂⟩ in m₂.toList do
    match m₁.find? k₂ with
    | .none => continue
    | .some v₁ => if v₁ == v₂ then result := result.erase k₂ else continue
  return result

/--
Difference between `m₁` and `m₂`.
Effectively `m₁ / m₂ × m₂ / m₁`.

- if the `Δ = (∅, ∅)`, then `m₁ = m₂`
- used for reporting delta between expected post state and the actual state post execution

Now that this is not a `Finmap`, this is probably defined somewhere in the API, fix later.
-/
def storageΔ (m₁ m₂ : PersistentAccountMap .EVM) : PersistentAccountMap .EVM × PersistentAccountMap .EVM :=
  (storageComplement m₁ m₂, storageComplement m₂ m₁)

section

/--
This section exists for debugging / testing mostly. It's somewhat ad-hoc.
-/

private def almostBEqButNotQuiteEvmYulState (s₁ s₂ : PersistentAccountMap .EVM) : Except String Bool := do
  if s₁ == s₂ then .ok true else throw "state mismatch"

/--
NB it is ever so slightly more convenient to be in `Except String Bool` here rather than `Option String`.

This is morally `s₁ == s₂` except we get a convenient way to both tune what is being compared
as well as report fine grained errors.
-/
private def almostBEqButNotQuite (s₁ s₂ : PersistentAccountMap .EVM) : Except String Bool := do
  discard <| almostBEqButNotQuiteEvmYulState s₁ s₂
  pure true -- Yes, we never return false, because we throw along the way. Yes, this is `Option`.

end

def executeTransaction
  (transaction : Transaction)
  (sender : AccountAddress)
  (s : EVM.State)
  (header : BlockHeader)
  : Except EVM.Exception EVM.State
:= do
  let _fuel : ℕ := s.accountMap.find? sender |>.elim ⟨0⟩ (·.balance) |>.toNat

  let (ypState, substate, statusCode, totalGasUsed) ←
    EVM.Υ _fuel
      s.accountMap
      header.baseFeePerGas
      header
      s.genesisBlockHeader
      s.blocks
      transaction
      sender

  -- as EIP 4788 (https://eips.ethereum.org/EIPS/eip-4788).

  let result : EVM.State :=
    { s with
      accountMap := ypState
      totalGasUsedInBlock := s.totalGasUsedInBlock + totalGasUsed.toNat
      transactionReceipts :=
        s.transactionReceipts.push
          ⟨ transaction.type
          , statusCode
          , s.totalGasUsedInBlock + totalGasUsed.toNat
          , bloomFilter substate.joinLogs
          , substate.logSeries
          ⟩
      substate
    }
  pure result

/-
  `baseFeePerGas`, `gasLimit` and `excessBlobGas` are used in transaction
  validation, so have to validated before.
-/
def validateHeaderBeforeTransactions
  (blocks : ProcessedBlocks)
  (header : BlockHeader)
  : Except EVM.Exception ProcessedBlock
:= do
  if header.parentHash = ⟨0⟩ then
    throw <| .BlockException .UNKNOWN_PARENT_ZERO

  let (some parent : Option ProcessedBlock) :=
    -- Usually the parent is the last processed block
    blocks.findRev? λ b ↦ b.hash = header.parentHash
    | throw <| .BlockException .UNKNOWN_PARENT

  let P_Hₗ := parent.blockHeader.gasLimit

  let ρ := 2; let τ := P_Hₗ / ρ; let ε := 8
  let νStar :=
    if parent.blockHeader.gasUsed < τ then
      (parent.blockHeader.baseFeePerGas * (τ - parent.blockHeader.gasUsed)) / τ
    else
      (parent.blockHeader.baseFeePerGas * (parent.blockHeader.gasUsed - τ)) / τ
  let ν :=
    if parent.blockHeader.gasUsed < τ then νStar / ε else max (νStar / ε) 1
  let expectedBaseFeePerGas :=
    if parent.blockHeader.gasUsed = τ then parent.blockHeader.baseFeePerGas else
    if parent.blockHeader.gasUsed < τ then parent.blockHeader.baseFeePerGas - ν else
      parent.blockHeader.baseFeePerGas + ν
  if
    header.gasLimit < 5000
      ∨ header.gasLimit ≥ P_Hₗ + P_Hₗ / 1024
      ∨ header.gasLimit ≤ P_Hₗ - P_Hₗ / 1024
  then
    throw <| .BlockException .INVALID_GASLIMIT
  if header.baseFeePerGas ≠ expectedBaseFeePerGas then
    throw <| .BlockException .INVALID_BASEFEE_PER_GAS
  if calcExcessBlobGas parent.blockHeader != header.excessBlobGas then
    throw <| .BlockException .INCORRECT_EXCESS_BLOB_GAS
  pure parent

def validateTransaction
  (σ : AccountMap .EVM)
  (chainId : ℕ)
  (header : BlockHeader)
  (totalGasUsedInBlock : ℕ)
  (T : Transaction)
  : Except EVM.Exception AccountAddress
:= do
  let H_f := header.baseFeePerGas
  if T.base.gasLimit.toNat + totalGasUsedInBlock > header.gasLimit then
    throw <| .TransactionException .GAS_ALLOWANCE_EXCEEDED
  if T.base.nonce.toNat ≥ 2^64-1 then
    throw <| .TransactionException .NONCE_IS_MAX

  let maxFeePerGas :=
    /-
      The test `lowGasPriceOldTypes_d0g0v0_Cancun` expects an
      `INSUFFICIENT_MAX_FEE_PER_GAS`, but its transaction doesn't have a
      `maxFeePerGas` field. We use `gasPrice` instead.
      See the 7th test for intrinsic validity, Yellow Paper, Chapter 7
    -/
    match T with
      | .dynamic t | .blob t => t.maxFeePerGas
      | .legacy t | .access t => t.gasPrice
  if H_f > maxFeePerGas.toNat then
    throw <| .TransactionException .INSUFFICIENT_MAX_FEE_PER_GAS

  let g₀ : ℕ := EVM.intrinsicGas T
  if T.base.gasLimit.toNat < g₀ then
    throw <| .TransactionException .INTRINSIC_GAS_TOO_LOW
  match T with
    | .dynamic t =>
      if t.maxPriorityFeePerGas > t.maxFeePerGas then
        throw <| .TransactionException .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
    | .blob bt => do
      if T.base.recipient = none then
        throw <| .TransactionException .TYPE_3_TX_CONTRACT_CREATION
      if bt.maxFeePerBlobGas.toNat < header.getBlobGasprice then
        .error (.TransactionException .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS)
      if bt.blobVersionedHashes.length > 6 then
        throw <| .TransactionException .TYPE_3_TX_BLOB_COUNT_EXCEEDED
      if bt.blobVersionedHashes.length = 0 then
        throw <| .TransactionException .TYPE_3_TX_ZERO_BLOBS
      if bt.blobVersionedHashes.any (λ h ↦ h[0]? != .some VERSIONED_HASH_VERSION_KZG) then
        throw <| .TransactionException .TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
    | _ => pure ()

  match T.base.recipient with
    | none => do
      let MAX_CODE_SIZE := 24576
      let MAX_INITCODE_SIZE := 2 * MAX_CODE_SIZE
      if T.base.data.size > MAX_INITCODE_SIZE then
        throw <| .TransactionException .INITCODE_SIZE_EXCEEDED
    | some _ => pure ()

  let some T_RLP := RLP (← (L_X T)) | throw <| .TransactionException .IllFormedRLP

  let r : ℕ := fromByteArrayBigEndian T.base.r
  let s : ℕ := fromByteArrayBigEndian T.base.s
  if 0 ≥ r ∨ r ≥ secp256k1n then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  if 0 ≥ s ∨ s > secp256k1n / 2 then throw <| .TransactionException .INVALID_SIGNATURE_VRS
  let v : ℕ := -- (324)
    match T with
      | .legacy t =>
        let w := t.w.toNat
        if w ∈ [27, 28] then
          w - 27
        else
          if w = 35 + chainId * 2 ∨ w = 36 + chainId * 2 then
            (w - 35) % 2
          else
            w
      | .access t | .dynamic t | .blob t => t.yParity.toNat
  if v ∉ [0, 1] then throw <| .TransactionException .INVALID_SIGNATURE_VRS

  let h_T := -- (318)
    match T with
      | .legacy _ => ffi.KEC T_RLP
      | _ => ffi.KEC <| ByteArray.mk #[T.type] ++ T_RLP

  let (S_T : AccountAddress) ← -- (323)
    match ECDSARECOVER h_T (ByteArray.mk #[.ofNat v]) T.base.r T.base.s with
      | .ok s =>
        pure <| Fin.ofNat _ <| fromByteArrayBigEndian <|
          (ffi.KEC s).extract 12 32 /- 160 bits = 20 bytes -/
      | .error s => throw <| .SenderRecoverError s

  -- "Also, with a slight abuse of notation ... "
  let (senderCode, senderNonce, senderBalance) :=
    match σ.find? S_T with
      | some sender => (sender.code, sender.nonce, sender.balance)
      | none =>
        dbg_trace s!"could not find sender {EvmYul.toHex S_T.toByteArray}"
        (.empty, ⟨0⟩, ⟨0⟩)

  if senderCode ≠ .empty then throw <| .TransactionException .SENDER_NOT_EOA
  if T.base.nonce < senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_LOW
  if T.base.nonce > senderNonce then
    throw <| .TransactionException .NONCE_MISMATCH_TOO_HIGH
  let v₀ ← do
    match T with
      | .legacy t | .access t =>
        if t.gasLimit.toNat * t.gasPrice.toNat > 2^256 then
          throw <| .TransactionException .GASLIMIT_PRICE_PRODUCT_OVERFLOW
        pure <| t.gasLimit * t.gasPrice + t.value
      | .dynamic t => pure <|  t.gasLimit * t.maxFeePerGas + t.value
      | .blob t =>
        pure <|
          t.gasLimit * t.maxFeePerGas
          + t.value
          + (UInt256.ofNat (getTotalBlobGas T)) * t.maxFeePerBlobGas
  if v₀ > senderBalance then
    throw <| .TransactionException .INSUFFICIENT_ACCOUNT_FUNDS

  pure S_T

 where
  L_X (T : Transaction) : Except EVM.Exception 𝕋 := -- (317)
    let accessEntryRLP : AccountAddress × Array UInt256 → 𝕋
      | ⟨a, s⟩ => .𝕃 [.𝔹 a.toByteArray, .𝕃 (s.map (.𝔹 ∘ UInt256.toByteArray)).toList]
    let accessEntriesRLP (aEs : List (AccountAddress × Array UInt256)) : 𝕋 :=
      .𝕃 (aEs.map accessEntryRLP)
    match T with
      | /- 0 -/ .legacy t =>
        if t.w.toNat ∈ [27, 28] then
          .ok ∘ .𝕃 ∘ List.map .𝔹 <|
            [ BE t.nonce.toNat -- Tₙ
            , BE t.gasPrice.toNat -- Tₚ
            , BE t.gasLimit.toNat -- T_g
            , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
              t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
            , BE t.value.toNat -- Tᵥ
            , t.data
            ]
        else
          if t.w = .ofNat (35 + chainId * 2) ∨ t.w = .ofNat (36 + chainId * 2) then
            .ok ∘ .𝕃 ∘ List.map .𝔹 <|
              [ BE t.nonce.toNat -- Tₙ
              , BE t.gasPrice.toNat -- Tₚ
              , BE t.gasLimit.toNat -- T_g
              , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
                t.recipient.option .empty AccountAddress.toByteArray -- Tₜ
              , BE t.value.toNat -- Tᵥ
              , t.data -- p
              , BE chainId
              , .empty
              , .empty
              ]
          else
            dbg_trace "IllFormedRLP legacy transacion: Tw = {t.w}; chainId = {chainId}"
            throw <| .TransactionException .IllFormedRLP

      | /- 1 -/ .access t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.gasPrice.toNat) -- Tₚ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- T_v
          , .𝔹 t.data  -- p
          , accessEntriesRLP t.accessList -- T_A
          ]
      | /- 2 -/ .dynamic t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP t.accessList -- T_A
          ]
      | /- 3 -/ .blob t =>
        .ok ∘ .𝕃 <|
          [ .𝔹 (BE t.chainId.toNat) -- T_c
          , .𝔹 (BE t.nonce.toNat) -- Tₙ
          , .𝔹 (BE t.maxPriorityFeePerGas.toNat) -- T_f
          , .𝔹 (BE t.maxFeePerGas.toNat) -- Tₘ
          , .𝔹 (BE t.gasLimit.toNat) -- T_g
          , -- If Tₜ is ∅ it becomes the RLP empty byte sequence and thus the member of 𝔹₀
            .𝔹 (t.recipient.option .empty AccountAddress.toByteArray) -- Tₜ
          , .𝔹 (BE t.value.toNat) -- Tᵥ
          , .𝔹 t.data -- p
          , accessEntriesRLP t.accessList -- T_A
          , .𝔹 (BE t.maxFeePerBlobGas.toNat)
          , .𝕃 (t.blobVersionedHashes.map .𝔹)
          ]

def validateBlock
  (state : EVM.State)
  (parentHeader : BlockHeader)
  (block : DeserializedBlock)
  : Except EVM.Exception Unit
:= do

  let MAX_BLOB_GAS_PER_BLOCK := 786432
  let blobGasUsed ← block.transactions.array.foldlM (init := 0) λ blobSum t ↦ do
    let blobSum := blobSum + getTotalBlobGas t
    if blobSum > MAX_BLOB_GAS_PER_BLOCK then
      throw <| .TransactionException .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
    pure blobSum

  if state.totalGasUsedInBlock ≠ block.blockHeader.gasUsed then
    throw <| .BlockException .INVALID_GAS_USED
  if block.blockHeader.timestamp ≤ parentHeader.timestamp then
    throw <| .BlockException .INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
  if block.blockHeader.number ≠ parentHeader.number + 1 then
    throw <| .BlockException .INVALID_BLOCK_NUMBER
  if block.blockHeader.extraData.size > 32 then
    throw <| .BlockException .EXTRA_DATA_TOO_BIG
  if block.blockHeader.gasLimit > 0x7fffffffffffffff then
    throw <| .BlockException .GASLIMIT_TOO_BIG
  if block.blockHeader.difficulty != 0 then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
  -- KEC (RLP []) = 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
  if
    0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347
      != block.blockHeader.ommersHash.toNat
  then
    throw <| .BlockException .IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS

  if blobGasUsed != block.blockHeader.blobGasUsed.toNat then
      throw <| .BlockException .INCORRECT_BLOB_GAS_USED

  if blobGasUsed > MAX_BLOB_GAS_PER_BLOCK then
    throw <| .BlockException .BLOB_GAS_USED_ABOVE_LIMIT

  if block.withdrawals.trieRoot ≠ block.blockHeader.withdrawalsRoot then
    throw <| .BlockException .INVALID_WITHDRAWALS_ROOT

  let computedStateHash : UInt256 :=
    stateTrieRoot state.accountMap.toPersistentAccountMap
    |>.option 0 fromByteArrayBigEndian
    |> .ofNat
  if block.blockHeader.stateRoot ≠ computedStateHash then
    throw <| .BlockException .INVALID_STATE_ROOT

  let expectedBloom := block.blockHeader.logsBloom
  let actualBloom := bloomFilter state.substate.joinLogs
  if expectedBloom ≠ actualBloom then
    throw <| .BlockException .INVALID_LOG_BLOOM
  if block.transactions.trieRoot ≠ block.blockHeader.transRoot then
    throw <| .BlockException .INVALID_TRANSACTIONS_ROOT

  let receiptsRoot :=
    TransactionReceipt.computeTrieRoot <|
      state.transactionReceipts.map TransactionReceipt.toTrieValue
  if receiptsRoot ≠ some block.blockHeader.receiptRoot then
    throw <| .BlockException .INVALID_RECEIPTS_ROOT

  pure ()

def deserializeRawBlock (rawBlock : RawBlock)
  : Except EVM.Exception DeserializedBlock
:= do
  let (blockHash, blockHeader, transactions, withdrawals) ← deserializeBlock rawBlock.rlp
  pure <| .mk blockHash blockHeader transactions withdrawals rawBlock.exception

/--
This assumes that the `transactions` are ordered, as they should be in the test suit.
-/
def processBlocks
  (pre : Pre)
  (blocks : RawBlocks)
  (genesisRLP : ByteArray)
  : Except EVM.Exception EVM.State
:= do
  let (genesisHash, genesisBlockHeader, _) ← deserializeBlock genesisRLP
  let state₀ :=
    { pre.toEVMState with
        genesisBlockHeader := genesisBlockHeader
        blocks :=
          #[
            ⟨ genesisHash
            , genesisBlockHeader
            , PersistentAccountMap.toAccountMap pre
            ⟩
          ]
    }
  let state ←
    blocks.foldlM (init := state₀)
      λ accState rawBlock ↦ do
        try
          let block ← deserializeRawBlock rawBlock
          let parent ←
            validateHeaderBeforeTransactions accState.blocks block.blockHeader
          let accState ← processBlock {accState with accountMap := parent.σ} block
          validateBlock accState parent.blockHeader block
          if ¬block.exception.isEmpty then
            throw <| .MissedExpectedException block.exception
          pure
            { accState with
                blocks :=
                  accState.blocks.push
                    ⟨block.hash, block.blockHeader, accState.accountMap⟩
            }
        catch e =>
          match e with
            | .MissedExpectedException _  => throw e
            | _ =>
              if rawBlock.exception.contains (repr e).pretty then
                -- dbg_trace
                --   s!"Expected exception: {String.intercalate "|" rawBlock.exception}; got exception: {repr e}"
                pure accState
              else
                throw e
  pure state
 where
  processBlock
    (s₀ : EVM.State)
    (block : DeserializedBlock)
    : Except EVM.Exception EVM.State
  := do
    -- Beacon call
    let s ← do
      let BEACON_ROOTS_ADDRESS : AccountAddress :=
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
      let SYSTEM_ADDRESS : AccountAddress :=
        0xfffffffffffffffffffffffffffffffffffffffe
      match s₀.accountMap.find? BEACON_ROOTS_ADDRESS with
        | none => pure s₀
        | some roots =>
          let beaconRootsAddressCode := roots.code
          let _fuel := 2^14
          -- the call does not count against the block’s gas limit
          let beaconCallResult :=
            EVM.Θ _fuel
              []
              .empty
              s₀.genesisBlockHeader
              s₀.blocks
              s₀.accountMap
              s₀.accountMap
              default
              SYSTEM_ADDRESS
              SYSTEM_ADDRESS
              BEACON_ROOTS_ADDRESS
              (.Code beaconRootsAddressCode)
              ⟨30000000⟩
              ⟨0xe8d4a51000⟩
              ⟨0⟩
              ⟨0⟩
              block.blockHeader.parentBeaconBlockRoot
              0
              block.blockHeader
              true
          let σ ←
            match beaconCallResult with
              | .ok (_, σ, _, _, _ /- can't fail-/, _) => pure σ
              | .error e => throw <| .ExecutionException e
          let s := {s₀ with accountMap := σ}
          pure s

    -- Transactions execution
    let s ←
      block.transactions.array.foldlM
        (λ s' trans ↦ do
          let S_T ←
            validateTransaction
              s'.accountMap
              chainId
              block.blockHeader
              s'.totalGasUsedInBlock
              trans
          executeTransaction trans S_T s' block.blockHeader
        )
        {s with totalGasUsedInBlock := 0, transactionReceipts := .empty}

    -- Withdrawals execution
    let σ := applyWithdrawals s.accountMap block.withdrawals.array

    pure { s with accountMap := σ }

/--
- `.none` on success
- `.some endState` on failure

NB we can throw away the final state if it coincided with the expected one, hence `.none`.
-/
def preImpliesPost (entry : TestEntry)
  : Except EVM.Exception (Option (PersistentAccountMap .EVM))
:= do
    let resultState ← processBlocks entry.pre entry.blocks entry.genesisRLP
    let lastAccountMap :=
      resultState.blocks.findRev? (·.hash == entry.lastblockhash)
      |>.option resultState.accountMap ProcessedBlock.σ
    let result : PersistentAccountMap .EVM :=
      lastAccountMap.foldl
        (λ r addr ⟨⟨nonce, balance, storage, code⟩, _, _⟩ ↦ r.insert addr ⟨nonce, balance, storage, code⟩) default
    let persistentAccountMap := resultState.accountMap.toPersistentAccountMap
    match entry.postState with
      | .Map post =>
        match almostBEqButNotQuite post result with
          | .error e =>
            dbg_trace e
            pure (.some persistentAccountMap) -- Feel free to inspect this error from `almostBEqButNotQuite`.
          | .ok _ => pure .none
      | .Hash h =>
        if stateTrieRoot persistentAccountMap ≠ h then
          dbg_trace "state hash mismatch"
          pure (.some persistentAccountMap)
        else
          pure .none

instance (priority := high) : Repr (PersistentAccountMap .EVM) := ⟨λ m _ ↦
  Id.run do
    let mut result := ""
    for (k, v) in m do
      result := result ++ s!"\nAccount[...{(EvmYul.toHex k.toByteArray) /-|>.takeRight 5-/}]\n"
      result := result ++ s!"balance: {v.balance}\nnonce: {v.nonce}\nstorage: \n"
      for (sk, sv) in v.storage do
        result := result ++ s!"{sk} → {sv}\n"
    return result⟩
 
def processTest (entry : TestEntry) (isTimed : Option (Nat × TestId) := .none) (verbose := true) : IO TestResult := do
  let tα ← if isTimed.isSome then IO.monoMsNow else pure 0
  let result := preImpliesPost entry
  let tω ← if isTimed.isSome then IO.monoMsNow else pure 0
  if let .some (thread, filepath, testname) := isTimed then
    IO.eprint s!"#{if thread / 10 == 1 then "" else " "}{thread} "
    IO.eprint s!"{testname} FROM {System.FilePath.mk (filepath.components.drop 3 |>.intersperse "/" |>.foldl (·++·) "")} "
    IO.eprintln s!"took: {(tω - tα).toFloat / 1000.0}s"
  pure <|
    match result with
    | .error err => .mkFailed s!"{repr err}"
    | .ok result => errorF <$> result
  where discardError : PersistentAccountMap .EVM → String := λ _ ↦ "ERROR."
        verboseError : PersistentAccountMap .EVM → String := λ σ ↦
          match entry.postState with
            | .Map post =>
              let (postSubActual, actualSubPost) := storageΔ post σ
              s!"\npost / actual: {repr postSubActual} \nactual / post: {repr actualSubPost}"
            | .Hash h =>
              s!"\npost: {EvmYul.toHex h} \nactual: {EvmYul.toHex <$> stateTrieRoot σ}"
        errorF := if verbose then verboseError else discardError

def processTests (tests : Array TestId) (isTimed : Option Nat := .none) :
                 IO (Array TestId × Array (TestId × TestResult)) := do
  let mut discarded : Array TestId := .empty
  let mut results : Array (TestId × TestResult) := .empty
  for testId@(path, testName) in tests do
    let file ← Lean.Json.fromFile path
    let test := Except.mapError Conform.Exception.CannotParse <| file.getObjValAs? TestEntry testName
    match test with
    | .error _ => IO.eprintln s!"Cannot parse: {testId}"
                  discarded := discarded.push testId
    | .ok test => if test.network.startsWith "Cancun"
                  then results := results.push (testId, ←processTest test <| isTimed <&> (·, testId))
  return (discarded, results)

end Conform

end EvmYul

```
`Conform/Wheels.lean`:

```lean
import Lean.Data.Json
import EvmYul.UInt256
import EvmYul.Wheels
import Batteries.Data.RBMap

import Mathlib.Data.Multiset.Sort

namespace Lean.Json

def getObjValAs!
  (self : Json) (α : Type) (key : String) [Inhabited α] [FromJson α] : α :=
  match self.getObjValAs? α key with
          | .error _ => panic! s!"Expected the key {key} in the map."
          | .ok pre  => pre

/--
Turn non-existance of the key into default initialisation.

This silences ONLY the `property not found:` error.
If the parsing of an existing value fails, we propagate the error.
-/
def getObjValAsD (j : Json) (α : Type) [FromJson α] (k : String) (D : α) : Except String α :=
  match j.getObjVal? k with
    | .error _   => pure D
    | .ok    val => fromJson? val

/--
`getObjValAsD! = getObjValAsD default` for inhabited types.
-/
def getObjValAsD! (j : Json) (α : Type) [FromJson α] [Inhabited α] (k : String) : Except String α :=
  getObjValAsD j α k default

def getObjVals?
  (self : Json) (α β : Type) [Ord α] [FromJson α] [FromJson β] : Except String (Batteries.RBMap α β compare) := do
  let keys ← Array.map Sigma.fst <$> RBNode.toArray <$> self.getObj?
  let mut result : Batteries.RBMap α β compare := ∅
  for k in keys do
    if let .ok key := FromJson.fromJson? k then
    result := result.insert key (← self.getObjValAs? β k)
  pure result

def fromFile (path : System.FilePath) : IO Json := do
  let .ok json ← Json.parse <$> IO.FS.readFile path | panic! s!"Failed to parse Json at: {path}"
  pure json

end Lean.Json

namespace EvmYul

namespace Conform

end Conform

section WithConform

open Conform

namespace UInt256

def fromBlob? (blob : Blob) : Except String UInt256 :=
  .ofNat <$> ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

def fromBlob! (blob : Blob) : UInt256 := fromBlob? blob |>.toOption.get!

end UInt256

def Nat.fromBlob? (blob : Blob) : Except String ℕ :=
  ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

namespace AccountAddress

def fromBlob? (s : Blob) : Except String AccountAddress := (Fin.ofNat _ ·.toNat) <$> UInt256.fromBlob? s

def fromBlob! (blob : Blob) : AccountAddress := fromBlob? blob |>.toOption.get!

end AccountAddress

end WithConform

namespace DebuggingAndProfiling

section

set_option autoImplicit true

unsafe def report [Inhabited β] (s : String) (f : α → β) (a : α) : β :=
  dbg_trace s!"BEGIN: {s}"
  let res := timeit s!"The function '{s}' took:" <| pure (f a)
  dbg_trace s!"END: {s}"
  unsafeIO res |>.toOption.get!

def testJsonParser (α : Type) [Repr α] [Lean.FromJson α] (s : String) : String :=
  match Lean.FromJson.fromJson? (α := α) <| (Lean.Json.parse s).toOption.getD Lean.Json.null with
    | .error e  => s!"err: {e}"
    | .ok    ok => s!"ok: {repr ok}"

end

end DebuggingAndProfiling

end EvmYul

def computeToList! {α}
                   [LE α] [IsTrans α (· ≤ ·)] [IsAntisymm α (· ≤ ·)] [IsTotal α (· ≤ ·)]
                   [DecidableRel (α := α) (· ≤ ·)] (m : Multiset α) : List α :=
  m.sort (· ≤ ·)

def Batteries.RBMap.partition {α β : Type} {cmp : α → α → Ordering}
  (t : Batteries.RBMap α β cmp) (p : α → β → Bool) : Batteries.RBMap α β cmp × Batteries.RBMap α β cmp :=
  (t.filter p, t.filter (λ k v ↦ not (p k v)))

namespace Std

namespace HashSet

def diff {α : Type} [DecidableEq α] [Hashable α] (a b : HashSet α) : HashSet α := Id.run do
  let mut res := a
  for elem in b do
    res := res.erase elem
  return res

end HashSet

end Std

```
`EvmYul.lean`:

```lean
import EvmYul.MachineState
import EvmYul.MachineStateOps
import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.Semantics
import EvmYul.SharedState
import EvmYul.SharedStateOps
import EvmYul.State
import EvmYul.StateOps
import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.PerformIO

import EvmYul.SHA256
import EvmYul.RIP160
import EvmYul.BN_ADD
import EvmYul.BN_MUL
import EvmYul.SNARKV
import EvmYul.BLAKE2_F

import EvmYul.Data.Stack

import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrimOps
import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.PrecompiledContracts
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants

import EvmYul.Maps.AccountMap
import EvmYul.Maps.ByteMap
import EvmYul.Maps.StorageMap

import EvmYul.State.Account
import EvmYul.State.AccountOps
import EvmYul.State.Block
import EvmYul.State.BlockHeader
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.SubstateOps
import EvmYul.State.Transaction
import EvmYul.State.Withdrawal
import EvmYul.State.TransactionOps
import EvmYul.State.TrieRoot

import EvmYul.Yul.Ast
import EvmYul.Yul.Exception
import EvmYul.Yul.Interpreter
import EvmYul.Yul.MachineState
import EvmYul.Yul.PrimOps
import EvmYul.Yul.SizeLemmas
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Yul.Wheels
import EvmYul.Yul.YulNotation

import EvmYul.SpongeHash.Keccak256

```
`EvmYul/BLAKE2_F.lean`:

```lean
import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/blake2_f.py", data]
  }

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s

```
`EvmYul/BN_ADD.lean`:

```lean
import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBN_ADD (x₀ y₀ x₁ y₁ : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ x₁ y₁
  where pythonCommandOfInput (x₀ y₀ x₁ y₁ : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/bn_add.py", x₀, y₀, x₁, y₁]
  }

def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  match blobBN_ADD (toHex x₀) (toHex y₀) (toHex x₁) (toHex y₁) with
    | "error" => .error "BN_ADD failed"
    | s => ByteArray.ofBlob s

```
`EvmYul/BN_MUL.lean`:

```lean
import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobBN_MUL (x₀ y₀ n : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ n
  where pythonCommandOfInput (x₀ y₀ n : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/bn_mul.py", x₀, y₀, n]
  }

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  match blobBN_MUL (toHex x₀) (toHex y₀) (toHex n) with
    | "error" => .error "BN_MUL failed"
    | s => ByteArray.ofBlob s

```
`EvmYul/Data/Stack.lean`:

```lean
namespace EvmYul

abbrev Stack (α : Type) := List α

namespace Stack

variable {α : Type}

def new : Stack α := []

def isEmpty (s : Stack α) := List.isEmpty s

def size (s : Stack α) : Nat := List.length s
def push (s : Stack α) (v : α) : Stack α := v :: s

def pop : Stack α → Option (Stack α × α)
  | hd :: tl => .some (tl, hd)
  | []       => .none

def pop2 : Stack α → Option (Stack α × α × α)
  | hd :: hd₁ :: tl => .some (tl, hd, hd₁)
  | _               => .none

def pop3 : Stack α → Option (Stack α × α × α × α)
  | hd :: hd₁ :: hd₂ :: tl => .some (tl, hd, hd₁, hd₂)
  | _                      => .none

def pop4 : Stack α → Option (Stack α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: tl => .some (tl, hd, hd₁, hd₂, hd₃)
  | _                             => .none

def pop5 : Stack α → Option (Stack α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄)
  | _                             => .none

def pop6 : Stack α → Option (Stack α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅)
  | _                             => .none

def pop7 : Stack α → Option (Stack α × α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: hd₆ :: tl =>
    .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆)
  | _                             => .none

section StackLemmas

variable {x : α} {s : Stack α}

@[simp]
theorem isEmpty_push_false : (s.push x).isEmpty = false := rfl

@[simp]
theorem isEmpty_nil : Stack.isEmpty (α := α) [] := rfl

@[simp]
theorem isEmpty_cons_false : Stack.isEmpty (α := α) (x :: s) = false := rfl

@[simp]
theorem size_nil : Stack.size (α := α) [] = 0 := rfl

@[simp]
theorem size_new : Stack.new.size (α := α) = 0 := rfl

@[simp]
theorem size_cons : Stack.size (α := α) (x :: s) = Stack.size s + 1 := rfl

theorem size_zero_iff_isEmpty_eq_true : s.size = 0 ↔ s.isEmpty = true := by
  cases s <;> simp

@[simp]
theorem size_push : (s.push x).size = s.size + 1 := rfl

@[simp]
theorem pop_push : (s.push x).pop = some (s, x) := rfl

end StackLemmas

instance {α} : Inhabited (Stack α) := ⟨Stack.new⟩
instance {α} [DecidableEq α] : DecidableEq (Stack α) := inferInstanceAs (DecidableEq (List α))
instance {α} : EmptyCollection (Stack α) := ⟨Stack.new⟩

end Stack

instance {α : Type} [ToString α] : ToString (Stack α) := inferInstanceAs (ToString (List α))

end EvmYul

```
`EvmYul/EVM/Exception.lean`:

```lean
import EvmYul.Wheels
import EvmYul.Maps.AccountMap
namespace EvmYul

namespace EVM

inductive ExecutionException where
  | OutOfFuel
  | InvalidInstruction
  | OutOfGass
  | BadJumpDestination
  | StackOverflow
  | StackUnderflow
  | InvalidMemoryAccess
  | StaticModeViolation
deriving BEq

instance : Repr ExecutionException where
  reprPrec s _ :=
    match s with
      | .OutOfFuel => "OutOfFuel"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfGass => "OutOfGass"
      | .BadJumpDestination => "BadJumpDestination"
      | .StackOverflow => "StackOverflow"
      | .StackUnderflow => "StackUnderflow"
      | .InvalidMemoryAccess => "InvalidMemoryAccess"
      | .StaticModeViolation => "StaticModeViolation"

inductive BlockException where
  | INCORRECT_EXCESS_BLOB_GAS
  | INCORRECT_BLOB_GAS_USED
  | INCORRECT_BLOCK_FORMAT -- No "Cancun" test needs this
  | BLOB_GAS_USED_ABOVE_LIMIT
  | INVALID_WITHDRAWALS_ROOT
  | IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS
  | RLP_STRUCTURES_ENCODING
  | IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS
  | RLP_INVALID_FIELD_OVERFLOW_64
  | RLP_INVALID_ADDRESS
  | GASLIMIT_TOO_BIG
  | INVALID_GAS_USED
  | UNKNOWN_PARENT_ZERO
  | EXTRA_DATA_TOO_BIG
  | INVALID_BLOCK_NUMBER
  | INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT
  | INVALID_GASLIMIT
  | INVALID_BASEFEE_PER_GAS
  | UNKNOWN_PARENT
  | INVALID_STATE_ROOT
  | INVALID_LOG_BLOOM
  | INVALID_TRANSACTIONS_ROOT
  | INVALID_RECEIPTS_ROOT

instance : Repr BlockException where
  reprPrec s _ :=
    match s with
      | .INCORRECT_EXCESS_BLOB_GAS => "INCORRECT_EXCESS_BLOB_GAS"
      | .INCORRECT_BLOB_GAS_USED => "INCORRECT_BLOB_GAS_USED"
      | .INCORRECT_BLOCK_FORMAT => "INCORRECT_BLOCK_FORMAT"
      | .BLOB_GAS_USED_ABOVE_LIMIT => "BLOB_GAS_USED_ABOVE_LIMIT"
      | .INVALID_WITHDRAWALS_ROOT => "INVALID_WITHDRAWALS_ROOT"
      | .IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS => "IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS"
      | .RLP_STRUCTURES_ENCODING => "RLP_STRUCTURES_ENCODING"
      | .IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS => "IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS"
      | .RLP_INVALID_FIELD_OVERFLOW_64 => "RLP_INVALID_FIELD_OVERFLOW_64"
      | .RLP_INVALID_ADDRESS => "RLP_INVALID_ADDRESS"
      | .GASLIMIT_TOO_BIG => "GASLIMIT_TOO_BIG"
      | .INVALID_GAS_USED => "INVALID_GAS_USED"
      | .UNKNOWN_PARENT_ZERO => "UNKNOWN_PARENT_ZERO"
      | .EXTRA_DATA_TOO_BIG => "EXTRA_DATA_TOO_BIG"
      | .INVALID_BLOCK_NUMBER => "INVALID_BLOCK_NUMBER"
      | .INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT => "INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT"
      | .INVALID_GASLIMIT => "INVALID_GASLIMIT"
      | .INVALID_BASEFEE_PER_GAS => "INVALID_BASEFEE_PER_GAS"
      | .UNKNOWN_PARENT => "UNKNOWN_PARENT"
      | .INVALID_STATE_ROOT => "INVALID_STATE_ROOT"
      | .INVALID_LOG_BLOOM => "INVALID_LOG_BLOOM"
      | .INVALID_TRANSACTIONS_ROOT => "INVALID_TRANSACTIONS_ROOT"
      | .INVALID_RECEIPTS_ROOT => "INVALID_RECEIPTS_ROOT"

inductive TransactionException where
  | IllFormedRLP
  | INVALID_SIGNATURE_VRS
  | NONCE_MISMATCH_TOO_LOW
  | NONCE_MISMATCH_TOO_HIGH
  | SENDER_NOT_EOA
  | INSUFFICIENT_ACCOUNT_FUNDS
  | PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS
  | TYPE_3_TX_ZERO_BLOBS
  | INTRINSIC_GAS_TOO_LOW
  | INSUFFICIENT_MAX_FEE_PER_BLOB_GAS
  | INITCODE_SIZE_EXCEEDED
  | NONCE_IS_MAX
  | TYPE_3_TX_BLOB_COUNT_EXCEEDED
  | GAS_ALLOWANCE_EXCEEDED
  | TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED
  | INSUFFICIENT_MAX_FEE_PER_GAS
  | TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH
  | TYPE_3_TX_CONTRACT_CREATION
  | GASLIMIT_PRICE_PRODUCT_OVERFLOW
  | RLP_INVALID_VALUE

/--
  TYPE_NOT_SUPPORTED - No "Cancun" test needs this
-/
instance : Repr TransactionException where
  reprPrec s _ :=
    match s with
      | .IllFormedRLP         => "IllFormedRLP"
      | .INVALID_SIGNATURE_VRS     => "INVALID_SIGNATURE_VRS"
      | .NONCE_MISMATCH_TOO_LOW   => "NONCE_MISMATCH_TOO_LOW"
      | .NONCE_MISMATCH_TOO_HIGH   => "NONCE_MISMATCH_TOO_HIGH"
      | .SENDER_NOT_EOA   => "SENDER_NOT_EOA"
      | .INSUFFICIENT_ACCOUNT_FUNDS => "INSUFFICIENT_ACCOUNT_FUNDS"
      | .PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS     => "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS"
      | .TYPE_3_TX_ZERO_BLOBS => "TYPE_3_TX_ZERO_BLOBS"
      | .INTRINSIC_GAS_TOO_LOW => "INTRINSIC_GAS_TOO_LOW"
      | .INSUFFICIENT_MAX_FEE_PER_BLOB_GAS => "INSUFFICIENT_MAX_FEE_PER_BLOB_GAS"
      | .INITCODE_SIZE_EXCEEDED => "INITCODE_SIZE_EXCEEDED"
      -- | .MAX_CODE_SIZE_EXCEEDED => "MAX_CODE_SIZE_EXCEEDED"
      | .NONCE_IS_MAX => "NONCE_IS_MAX"
      | .TYPE_3_TX_BLOB_COUNT_EXCEEDED => "TYPE_3_TX_BLOB_COUNT_EXCEEDED"
      | .GAS_ALLOWANCE_EXCEEDED => "GAS_ALLOWANCE_EXCEEDED"
      | .TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED => "TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"
      | .INSUFFICIENT_MAX_FEE_PER_GAS => "INSUFFICIENT_MAX_FEE_PER_GAS"
      | .TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH => "TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH"
      | .TYPE_3_TX_CONTRACT_CREATION => "TYPE_3_TX_CONTRACT_CREATION"
      | .GASLIMIT_PRICE_PRODUCT_OVERFLOW => "GASLIMIT_PRICE_PRODUCT_OVERFLOW"
      | .RLP_INVALID_VALUE => "RLP_INVALID_VALUE"

inductive Exception where
  | ExecutionException :     ExecutionException → Exception
  | NotEncodableRLP :                             Exception
  | TransactionException : TransactionException → Exception
  | SenderRecoverError :                 String → Exception
  | BlockException :             BlockException → Exception
  | MissedExpectedException :       List String → Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .ExecutionException ee =>       "Execution exception: " ++ repr ee
      | .NotEncodableRLP =>             "NotEncodableRLP"
      | .TransactionException e =>      "TransactionException." ++ repr e
      | .SenderRecoverError s =>        "SenderRecoverError." ++ s
      | .BlockException be =>           "BlockException." ++ repr be
      | .MissedExpectedException mee =>
        "Missed expected exception: " ++ String.intercalate "|" mee

end EVM

end EvmYul

```
`EvmYul/EVM/Gas.lean`:

```lean
import Mathlib.Data.Nat.Log

import EvmYul.EVM.State
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace EVM

/-
Appendix G. Fee Schedule
-/

namespace InstructionGasGroups

def Wzero : List (Operation .EVM) := [.STOP, .RETURN, .REVERT]

def Wbase : List (Operation .EVM) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .BLOBBASEFEE, .PUSH0]

def Wverylow : List (Operation .EVM) := [
  .ADD, .SUB, .NOT, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR,
  .CALLDATALOAD, .MLOAD, .MSTORE, .MSTORE8
  ] ++ pushInstrsWithoutZero
    ++ dupInstrs
    ++ swapInstrs
  where
    pushInstrsWithoutZero : List (Operation .EVM) := [
      .PUSH1, .PUSH2, .PUSH3, .PUSH4, .PUSH5,
      .PUSH6, .PUSH7, .PUSH8, .PUSH9, .PUSH10,
      .PUSH11, .PUSH12, .PUSH13, .PUSH14, .PUSH15,
      .PUSH16, .PUSH17, .PUSH18, .PUSH19, .PUSH20,
      .PUSH21, .PUSH22, .PUSH23, .PUSH24, .PUSH25,
      .PUSH26, .PUSH27, .PUSH28, .PUSH29, .PUSH30,
      .PUSH31, .PUSH32
    ]
    dupInstrs : List (Operation .EVM) := [
      .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
      .DUP6, .DUP7, .DUP8, .DUP9, .DUP10,
      .DUP11, .DUP12, .DUP13, .DUP14, .DUP15,
      .DUP16
    ]
    swapInstrs : List (Operation .EVM) := [
      .SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5,
      .SWAP6, .SWAP7, .SWAP8, .SWAP9, .SWAP10,
      .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15,
      .SWAP16
    ]

def Wlow : List (Operation .EVM) := [
  .MUL, .DIV, .SDIV, .MOD, .SMOD, .SIGNEXTEND, .SELFBALANCE
]

def Wmid : List (Operation .EVM) := [
  .ADDMOD, .MULMOD, .JUMP
]

def Whigh : List (Operation .EVM) := [
  .JUMPI
]

def Wcopy : List (Operation .EVM) := [
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY
]

def Wcall : List (Operation .EVM) := [
  .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL
]

def Wextaccount : List (Operation .EVM) := [
  .BALANCE, .EXTCODESIZE, .EXTCODEHASH
]

end InstructionGasGroups

section Gas

open GasConstants InstructionGasGroups

/--
(328)
-/
def Cₘ (a : UInt256) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
def Csstore (s : EVM.State) : ℕ :=
  let { stack := μₛ, accountMap := σ, σ₀ := σ₀, executionEnv.codeOwner := Iₐ, .. } := s
  let { storage := σ_Iₐ, .. } := σ.find! Iₐ
  let storeAddr := μₛ[0]!
  let v₀ :=
    match σ₀.find? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.findD storeAddr ⟨0⟩
  let v := σ_Iₐ.findD storeAddr ⟨0⟩
  let v' := μₛ[1]!
  let loadComponent :=
    if s.substate.accessedStorageKeys.contains (Iₐ, storeAddr) then
      0
    else
      Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v             then Gwarmaccess else
                        if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else
                        /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  loadComponent + storeComponent

def Ctstore : ℕ :=
  let loadComponent := 0
  let storeComponent := Gwarmaccess
  loadComponent + storeComponent

/--
(328)
-/
def Caccess (a : AccountAddress) (A : Substate) : ℕ :=
  if A.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

/--
CHECK -
In YP we have `Cselfdestruct(σ, μ)`; if we were to compute `Aₐ` that we need, we would need an
address in `σ` - is this address supposed to be obvious?
CURRENT SOLUTION -
We take `EVM.State`.
-/
def Cselfdestruct (s : EVM.State) : ℕ :=
  let r := AccountAddress.ofUInt256 s.stack[0]!
  let { substate.accessedAccounts := Aₐ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let c_cold := if Aₐ.contains r then 0 else Gcoldaccountaccess
  let c_new :=
    if State.dead σ r ∧ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
      Gnewaccount
    else 0
  Gselfdestruct + c_cold + c_new

/--
NB Assumes stack coherency.
-/
def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) : ℕ :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

def Ctload : ℕ :=
  Gwarmaccess

/--
(331)
-/
def L (n : ℕ) : ℕ := n - (n / 64)

def Cnew (t : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) : ℕ :=
  if EvmYul.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

def Cxfer (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then Gcallvalue else 0

def Cextra (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  Caccess t A + Cxfer val + Cnew r val σ

def Cgascap (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) :=
  if μ.gasAvailable.toNat >= Cextra t r val σ A then
    min (L <| (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat
  else
    g.toNat

def Ccallgas (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  match val with
    | ⟨0⟩ => Cgascap t r val g σ μ A
    | _ => Cgascap t r val g σ μ A + GasConstants.Gcallstipend

/--
NB Assumes stack coherence.
-/
def Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  Cgascap t r val g σ μ A + Cextra t r val σ A

/--
(65)
-/
def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

def intrinsicGas (T : Transaction) : ℕ :=
  let g₀_data :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let g₀_create : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + R (T.base.data.size)
    else 0

  let g₀_accessList : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  g₀_data + g₀_create + GasConstants.Gtransaction + g₀_accessList

/--
H.1. Gas Cost - the third summand.

NB Stack accesses are assumed guarded here and we access with `!`.
This is for keeping in sync with the way the YP is structures, at least for the time being.
-/
def C' (s : State) (instr : Operation .EVM) : ℕ :=
  let { accountMap := σ, stack := μₛ, substate := A, toMachineState := μ, executionEnv := I, ..} := s
  match instr with
    | .SSTORE => Csstore s
    | .TSTORE => Ctstore
    | .EXP => let μ₁ := μₛ[1]!; if μ₁ == ⟨0⟩ then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 μ₁.toNat) -- TODO(check) I think this floors by itself. cf. H.1. YP.
    | .EXTCODECOPY => Caccess (AccountAddress.ofUInt256 μₛ[0]!) A + Gcopy * ((μₛ[3]!.toNat + 31) / 32)
    | .LOG0 => Glog + Glogdata * μₛ[1]!.toNat
    | .LOG1 => Glog + Glogdata * μₛ[1]!.toNat +     Glogtopic
    | .LOG2 => Glog + Glogdata * μₛ[1]!.toNat + 2 * Glogtopic
    | .LOG3 => Glog + Glogdata * μₛ[1]!.toNat + 3 * Glogtopic
    | .LOG4 => Glog + Glogdata * μₛ[1]!.toNat + 4 * Glogtopic
    | .SELFDESTRUCT => Cselfdestruct s
    | .CREATE => Gcreate + R μₛ[2]!.toNat
    | .CREATE2 => let μ₂ := μₛ[2]!; Gcreate + Gkeccak256word * ((μ₂.toNat + 31) / 32) + R μ₂.toNat
    | .KECCAK256 => Gkeccak256 + Gkeccak256word * ((μₛ[1]!.toNat + 31) / 32)
    | .JUMPDEST => Gjumpdest
    | .SLOAD => Csload μₛ A I
    | .TLOAD => Ctload
    | .BLOCKHASH => Gblockhash
    /-
      By `μₛ[2]` the YP means the value that is to be transferred,
      not what happens to be on the stack at index 2. Therefore it is 0 for
      `DELEGATECALL` and `STATICCALL`.
    -/
    | .CALL =>         Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .CALLCODE =>     Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner μₛ[2]! μₛ[0]! σ μ A
    | .DELEGATECALL => Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner    ⟨0⟩ μₛ[0]! σ μ A
    | .STATICCALL =>   Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!)    ⟨0⟩ μₛ[0]! σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then Gverylow + Gcopy * ((μₛ[2]!.toNat + 31) / 32) else
      if w ∈ Wextaccount then Caccess (AccountAddress.ofUInt256 μₛ[0]!) A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      0

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/

def memoryExpansionCost (s : EVM.State) (instr : Operation .EVM) : ℕ :=
  Cₘ μᵢ' - Cₘ s.toMachineState.activeWords
 where
  μᵢ' : UInt256 :=
    match instr with
      | .KECCAK256 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CALLDATACOPY | .CODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MCOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat (max s.stack[0]!.toNat s.stack[1]!.toNat) s.stack[2]!.toNat
      | .EXTCODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[3]!.toNat
      | .RETURNDATACOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MLOAD | .MSTORE => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 32
      | .MSTORE8 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 1
      | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
        .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CREATE | .CREATE2 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[2]!.toNat
      | .CALL | .CALLCODE =>
        let m : ℕ := MachineState.M s.toMachineState.activeWords.toNat s.stack[3]!.toNat s.stack[4]!.toNat
        .ofNat <| MachineState.M m s.stack[5]!.toNat s.stack[6]!.toNat
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ:= MachineState.M s.toMachineState.activeWords.toNat s.stack[2]!.toNat s.stack[3]!.toNat
        .ofNat <| MachineState.M m s.stack[4]!.toNat s.stack[5]!.toNat
      | .RETURN | .REVERT => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | _ => s.toMachineState.activeWords

end Gas

end EVM

end EvmYul

```
`EvmYul/EVM/GasConstants.lean`:

```lean
import EvmYul.UInt256

namespace GasConstants

section FeeSchedule

def Gzero : ℕ              := 0
def Gjumpdest : ℕ          := 1
def Gbase : ℕ              := 2
def Gverylow : ℕ           := 3
def Glow : ℕ               := 5
def Gmid : ℕ               := 8
def Ghigh : ℕ              := 10
def Gwarmaccess : ℕ        := 100
def Gaccesslistaddress : ℕ := 2400
def Gaccessliststorage : ℕ := 1900
def Gcoldaccountaccess : ℕ := 2600
def Gcoldsload : ℕ         := 2100
def Gsset : ℕ              := 20000
def Gsreset : ℕ            := 2900
def Rsclear : ℕ            := 4800
def Gselfdestruct : ℕ      := 5000
def Gcreate : ℕ            := 32000
def Gcodedeposit : ℕ       := 200
def Ginitcodeword : ℕ      := 2
def Gcallvalue : ℕ         := 9000
def Gcallstipend : ℕ       := 2300
def Gnewaccount : ℕ        := 25000
def Gexp : ℕ               := 10
def Gexpbyte : ℕ           := 50
def Gmemory : ℕ            := 3
def Gtxcreate : ℕ          := 32000
def Gtxdatazero : ℕ        := 4
def Gtxdatanonzero : ℕ     := 16
def Gtransaction : ℕ       := 21000
def Glog : ℕ               := 375
def Glogdata : ℕ           := 8
def Glogtopic : ℕ          := 375
def Gkeccak256 : ℕ         := 30
def Gkeccak256word : ℕ     := 6
def Gcopy : ℕ              := 3
def Gblockhash : ℕ         := 20
def HASH_OPCODE_GAS : ℕ    := 3

end FeeSchedule

end GasConstants

```
`EvmYul/EVM/Instr.lean`:

```lean
import EvmYul.Operations

namespace EvmYul

namespace EVM

open Operation

def serializeStopArithInstr : SAOp .EVM → UInt8
  | .STOP       => 0x00
  | .ADD        => 0x01
  | .MUL        => 0x02
  | .SUB        => 0x03
  | .DIV        => 0x04
  | .SDIV       => 0x05
  | .MOD        => 0x06
  | .SMOD       => 0x07
  | .ADDMOD     => 0x08
  | .MULMOD     => 0x09
  | .EXP        => 0x0a
  | .SIGNEXTEND => 0x0b

def serializeCompBitInstr : CBLOp .EVM → UInt8
  | .LT     => 0x10
  | .GT     => 0x11
  | .SLT    => 0x12
  | .SGT    => 0x13
  | .EQ     => 0x14
  | .ISZERO => 0x15
  | .AND    => 0x16
  | .OR     => 0x17
  | .XOR    => 0x18
  | .NOT    => 0x19
  | .BYTE   => 0x1a
  | .SHL    => 0x1b
  | .SHR    => 0x1c
  | .SAR    => 0x1d

def serializeKeccakInstr : KOp .EVM → UInt8
  | .KECCAK256 => 0x20

def serializeEnvInstr : EOp .EVM → UInt8
  | .ADDRESS        => 0x30
  | .BALANCE        => 0x31
  | .ORIGIN         => 0x32
  | .CALLER         => 0x33
  | .CALLVALUE      => 0x34
  | .CALLDATALOAD   => 0x35
  | .CALLDATASIZE   => 0x36
  | .CALLDATACOPY   => 0x37
  | .CODESIZE       => 0x38
  | .CODECOPY       => 0x39
  | .GASPRICE       => 0x3a
  | .EXTCODESIZE    => 0x3b
  | .EXTCODECOPY    => 0x3c
  | .RETURNDATASIZE => 0x3d
  | .RETURNDATACOPY => 0x3e
  | .EXTCODEHASH    => 0x3f

def serializeBlockInstr : BOp .EVM → UInt8
  | .BLOCKHASH   => 0x40
  | .COINBASE    => 0x41
  | .TIMESTAMP   => 0x42
  | .NUMBER      => 0x43
  | .PREVRANDAO  => 0x44
  | .GASLIMIT    => 0x45
  | .CHAINID     => 0x46
  | .SELFBALANCE => 0x47
  | .BASEFEE     => 0x48
  | .BLOBHASH    => 0x49
  | .BLOBBASEFEE => 0x4a

def serializeStackMemFlowInstr : SMSFOp .EVM → UInt8
  | .POP      => 0x50
  | .MLOAD    => 0x51
  | .MSTORE   => 0x52
  | .MSTORE8  => 0x53
  | .SLOAD    => 0x54
  | .SSTORE   => 0x55
  | .JUMP     => 0x56
  | .JUMPI    => 0x57
  | .PC       => 0x58
  | .MSIZE    => 0x59
  | .GAS      => 0x5a
  | .JUMPDEST => 0x5b
  | .TLOAD    => 0x5c
  | .TSTORE   => 0x5d
  | .MCOPY    => 0x5e

def serializePushInstr : POp → UInt8
  | .PUSH0  => 0x5f
  | .PUSH1  => 0x60
  | .PUSH2  => 0x61
  | .PUSH3  => 0x62
  | .PUSH4  => 0x63
  | .PUSH5  => 0x64
  | .PUSH6  => 0x65
  | .PUSH7  => 0x66
  | .PUSH8  => 0x67
  | .PUSH9  => 0x68
  | .PUSH10 => 0x69
  | .PUSH11 => 0x6a
  | .PUSH12 => 0x6b
  | .PUSH13 => 0x6c
  | .PUSH14 => 0x6d
  | .PUSH15 => 0x6e
  | .PUSH16 => 0x6f
  | .PUSH17 => 0x70
  | .PUSH18 => 0x71
  | .PUSH19 => 0x72
  | .PUSH20 => 0x73
  | .PUSH21 => 0x74
  | .PUSH22 => 0x75
  | .PUSH23 => 0x76
  | .PUSH24 => 0x77
  | .PUSH25 => 0x78
  | .PUSH26 => 0x79
  | .PUSH27 => 0x7a
  | .PUSH28 => 0x7b
  | .PUSH29 => 0x7c
  | .PUSH30 => 0x7d
  | .PUSH31 => 0x7e
  | .PUSH32 => 0x7f

def serializeDupInstr : DOp → UInt8
  | .DUP1  => 0x80
  | .DUP2  => 0x81
  | .DUP3  => 0x82
  | .DUP4  => 0x83
  | .DUP5  => 0x84
  | .DUP6  => 0x85
  | .DUP7  => 0x86
  | .DUP8  => 0x87
  | .DUP9  => 0x88
  | .DUP10 => 0x89
  | .DUP11 => 0x8a
  | .DUP12 => 0x8b
  | .DUP13 => 0x8c
  | .DUP14 => 0x8d
  | .DUP15 => 0x8e
  | .DUP16 => 0x8f

def serializeSwapInstr : ExOp → UInt8
  | .SWAP1  => 0x90
  | .SWAP2  => 0x91
  | .SWAP3  => 0x92
  | .SWAP4  => 0x93
  | .SWAP5  => 0x94
  | .SWAP6  => 0x95
  | .SWAP7  => 0x96
  | .SWAP8  => 0x97
  | .SWAP9  => 0x98
  | .SWAP10 => 0x99
  | .SWAP11 => 0x9a
  | .SWAP12 => 0x9b
  | .SWAP13 => 0x9c
  | .SWAP14 => 0x9d
  | .SWAP15 => 0x9e
  | .SWAP16 => 0x9f

def serializeLogInstr : LOp .EVM → UInt8
  | .LOG0 => 0xa0
  | .LOG1 => 0xa1
  | .LOG2 => 0xa2
  | .LOG3 => 0xa3
  | .LOG4 => 0xa4

def serializeSysInstr : SOp .EVM → UInt8
  | .CREATE       => 0xf0
  | .CALL         => 0xf1
  | .CALLCODE     => 0xf2
  | .RETURN       => 0xf3
  | .DELEGATECALL => 0xf4
  | .CREATE2      => 0xf5
  | .STATICCALL   => 0xfa
  | .REVERT       => 0xfd
  | .INVALID      => 0xfe
  | .SELFDESTRUCT => 0xff

def serializeInstr : Operation .EVM → UInt8
  | .StopArith a    => serializeStopArithInstr a
  | .CompBit e      => serializeCompBitInstr e
  | .Keccak k       => serializeKeccakInstr k
  | .Env e          => serializeEnvInstr e
  | .Block b        => serializeBlockInstr b
  | .StackMemFlow m => serializeStackMemFlowInstr m
  | .Push p         => serializePushInstr p
  | .Dup d          => serializeDupInstr d
  | .Exchange e     => serializeSwapInstr e
  | .Log l          => serializeLogInstr l
  | .System s       => serializeSysInstr s

def δ : Operation .EVM → Option ℕ
  | .STOP           => some 0
  | .ADD            => some 2
  | .MUL            => some 2
  | .SUB            => some 2
  | .DIV            => some 2
  | .SDIV           => some 2
  | .MOD            => some 2
  | .SMOD           => some 2
  | .ADDMOD         => some 3
  | .MULMOD         => some 3
  | .EXP            => some 2
  | .SIGNEXTEND     => some 2
  | .LT             => some 2
  | .GT             => some 2
  | .SLT            => some 2
  | .SGT            => some 2
  | .EQ             => some 2
  | .ISZERO         => some 1
  | .AND            => some 2
  | .OR             => some 2
  | .XOR            => some 2
  | .NOT            => some 1
  | .BYTE           => some 2
  | .SHL            => some 2
  | .SHR            => some 2
  | .SAR            => some 2
  | .KECCAK256      => some 2
  | .ADDRESS        => some 0
  | .BALANCE        => some 1
  | .ORIGIN         => some 0
  | .CALLER         => some 0
  | .CALLVALUE      => some 0
  | .CALLDATALOAD   => some 1
  | .CALLDATASIZE   => some 0
  | .CALLDATACOPY   => some 3
  | .CODESIZE       => some 0
  | .CODECOPY       => some 3
  | .GASPRICE       => some 0
  | .EXTCODESIZE    => some 1
  | .EXTCODECOPY    => some 4
  | .RETURNDATASIZE => some 0
  | .RETURNDATACOPY => some 3
  | .EXTCODEHASH    => some 1
  | .BLOCKHASH      => some 1
  | .COINBASE       => some 0
  | .TIMESTAMP      => some 0
  | .NUMBER         => some 0
  | .PREVRANDAO     => some 0
  | .GASLIMIT       => some 0
  | .CHAINID        => some 0
  | .SELFBALANCE    => some 0
  | .BASEFEE        => some 0
  | .BLOBHASH       => some 1
  | .BLOBBASEFEE    => some 0
  | .POP            => some 1
  | .MLOAD          => some 1
  | .MSTORE         => some 2
  | .MSTORE8        => some 2
  | .SLOAD          => some 1
  | .SSTORE         => some 2
  | .PC             => some 0
  | .MSIZE          => some 0
  | .GAS            => some 0
  | .Push _         => some 0
  | .DUP1           => some 1
  | .DUP2           => some 2
  | .DUP3           => some 3
  | .DUP4           => some 4
  | .DUP5           => some 5
  | .DUP6           => some 6
  | .DUP7           => some 7
  | .DUP8           => some 8
  | .DUP9           => some 9
  | .DUP10          => some 10
  | .DUP11          => some 11
  | .DUP12          => some 12
  | .DUP13          => some 13
  | .DUP14          => some 14
  | .DUP15          => some 15
  | .DUP16          => some 16
  | .SWAP1          => some 2
  | .SWAP2          => some 3
  | .SWAP3          => some 4
  | .SWAP4          => some 5
  | .SWAP5          => some 6
  | .SWAP6          => some 7
  | .SWAP7          => some 8
  | .SWAP8          => some 9
  | .SWAP9          => some 10
  | .SWAP10         => some 11
  | .SWAP11         => some 12
  | .SWAP12         => some 13
  | .SWAP13         => some 14
  | .SWAP14         => some 15
  | .SWAP15         => some 16
  | .SWAP16         => some 17
  | .LOG0           => some 2
  | .LOG1           => some 3
  | .LOG2           => some 4
  | .LOG3           => some 5
  | .LOG4           => some 6
  | .JUMP           => some 1
  | .JUMPI          => some 2
  | .JUMPDEST       => some 0
  | .TLOAD          => some 1
  | .TSTORE         => some 2
  | .MCOPY          => some 3
  | .CREATE         => some 3
  | .CALL           => some 7
  | .CALLCODE       => some 7
  | .RETURN         => some 2
  | .DELEGATECALL   => some 6
  | .CREATE2        => some 4
  | .STATICCALL     => some 6
  | .REVERT         => some 2
  | .INVALID        => none
  | .SELFDESTRUCT   => some 1

def α : Operation .EVM → Option ℕ
  | .STOP => some 0
  | .ADD => some 1
  | .MUL => some 1
  | .SUB => some 1
  | .DIV => some 1
  | .SDIV => some 1
  | .MOD => some 1
  | .SMOD => some 1
  | .ADDMOD => some 1
  | .MULMOD => some 1
  | .EXP => some 1
  | .SIGNEXTEND  => some 1
  | .LT => some 1
  | .GT => some 1
  | .SLT  => some 1
  | .SGT => some 1
  | .EQ => some 1
  | .ISZERO => some 1
  | .AND => some 1
  | .OR => some 1
  | .XOR => some 1
  | .NOT => some 1
  | .BYTE => some 1
  | .SHL => some 1
  | .SHR => some 1
  | .SAR => some 1
  | .KECCAK256 => some 1
  | .ADDRESS => some 1
  | .BALANCE => some 1
  | .ORIGIN => some 1
  | .CALLER => some 1
  | .CALLVALUE => some 1
  | .CALLDATALOAD  => some 1
  | .CALLDATASIZE => some 1
  | .CALLDATACOPY => some 0
  | .CODESIZE  => some 1
  | .CODECOPY => some 0
  | .GASPRICE => some 1
  | .EXTCODESIZE  => some 1
  | .EXTCODECOPY => some 0
  | .RETURNDATASIZE  => some 1
  | .RETURNDATACOPY => some 0
  | .EXTCODEHASH => some 1
  | .BLOCKHASH => some 1
  | .COINBASE => some 1
  | .TIMESTAMP => some 1
  | .NUMBER => some 1
  | .PREVRANDAO => some 1
  | .GASLIMIT => some 1
  | .CHAINID => some 1
  | .SELFBALANCE => some 1
  | .BASEFEE => some 1
  | .BLOBHASH => some 1
  | .BLOBBASEFEE => some 1
  | .POP => some 0
  | .MLOAD => some 1
  | .MSTORE => some 0
  | .MSTORE8 => some 0
  | .SLOAD => some 1
  | .SSTORE => some 0
  | .PC => some 1
  | .MSIZE => some 1
  | .GAS => some 1
  | .JUMP => some 0
  | .JUMPI => some 0
  | .JUMPDEST => some 0
  | .TLOAD => some 1
  | .TSTORE => some 0
  | .MCOPY => some 0
  | .Push _ => some 1
  | .DUP1 => some 2
  | .DUP2 => some 3
  | .DUP3 => some 4
  | .DUP4 => some 5
  | .DUP5 => some 6
  | .DUP6 => some 7
  | .DUP7 => some 8
  | .DUP8 => some 9
  | .DUP9 => some 10
  | .DUP10 => some 11
  | .DUP11 => some 12
  | .DUP12 => some 13
  | .DUP13 => some 14
  | .DUP14 => some 15
  | .DUP15 => some 16
  | .DUP16 => some 17
  | .SWAP1 => some 2
  | .SWAP2 => some 3
  | .SWAP3 => some 4
  | .SWAP4 => some 5
  | .SWAP5 => some 6
  | .SWAP6 => some 7
  | .SWAP7 => some 8
  | .SWAP8 => some 9
  | .SWAP9 => some 10
  | .SWAP10 => some 11
  | .SWAP11 => some 12
  | .SWAP12 => some 13
  | .SWAP13 => some 14
  | .SWAP14 => some 15
  | .SWAP15 => some 16
  | .SWAP16 => some 17
  | .Log _ => some 0
  | .CREATE => some 1
  | .CALL => some 1
  | .CALLCODE => some 1
  | .RETURN => some 0
  | .DELEGATECALL => some 1
  | .CREATE2 => some 1
  | .STATICCALL => some 1
  | .REVERT => some 0
  | .INVALID => none
  | .SELFDESTRUCT => some 0

def parseInstr : UInt8 → Option (Operation .EVM)
  | 0x00 => some .STOP
  | 0x01 => some .ADD
  | 0x02 => some .MUL
  | 0x03 => some .SUB
  | 0x04 => some .DIV
  | 0x05 => some .SDIV
  | 0x06 => some .MOD
  | 0x07 => some .SMOD
  | 0x08 => some .ADDMOD
  | 0x09 => some .MULMOD
  | 0x0a => some .EXP
  | 0x0b => some .SIGNEXTEND

  | 0x10 => some .LT
  | 0x11 => some .GT
  | 0x12 => some .SLT
  | 0x13 => some .SGT
  | 0x14 => some .EQ
  | 0x15 => some .ISZERO
  | 0x16 => some .AND
  | 0x17 => some .OR
  | 0x18 => some .XOR
  | 0x19 => some .NOT
  | 0x1a => some .BYTE
  | 0x1b => some .SHL
  | 0x1c => some .SHR
  | 0x1d => some .SAR

  | 0x20 => some .KECCAK256

  | 0x30 => some .ADDRESS
  | 0x31 => some .BALANCE
  | 0x32 => some .ORIGIN
  | 0x33 => some .CALLER
  | 0x34 => some .CALLVALUE
  | 0x35 => some .CALLDATALOAD
  | 0x36 => some .CALLDATASIZE
  | 0x37 => some .CALLDATACOPY
  | 0x38 => some .CODESIZE
  | 0x39 => some .CODECOPY
  | 0x3a => some .GASPRICE
  | 0x3b => some .EXTCODESIZE
  | 0x3c => some .EXTCODECOPY
  | 0x3d => some .RETURNDATASIZE
  | 0x3e => some .RETURNDATACOPY
  | 0x3f => some .EXTCODEHASH

  | 0x40 => some .BLOCKHASH
  | 0x41 => some .COINBASE
  | 0x42 => some .TIMESTAMP
  | 0x43 => some .NUMBER
  | 0x44 => some .PREVRANDAO
  | 0x45 => some .GASLIMIT
  | 0x46 => some .CHAINID
  | 0x47 => some .SELFBALANCE
  | 0x48 => some .BASEFEE
  | 0x49 => some .BLOBHASH
  | 0x4a => some .BLOBBASEFEE

  | 0x50 => some .POP
  | 0x51 => some .MLOAD
  | 0x52 => some .MSTORE
  | 0x53 => some .MSTORE8
  | 0x54 => some .SLOAD
  | 0x55 => some .SSTORE
  | 0x56 => some .JUMP
  | 0x57 => some .JUMPI
  | 0x58 => some .PC
  | 0x59 => some .MSIZE
  | 0x5a => some .GAS
  | 0x5b => some .JUMPDEST
  | 0x5c => some .TLOAD
  | 0x5d => some .TSTORE
  | 0x5e => some .MCOPY

  | 0x5f => some .PUSH0
  | 0x60 => some .PUSH1
  | 0x61 => some .PUSH2
  | 0x62 => some .PUSH3
  | 0x63 => some .PUSH4
  | 0x64 => some .PUSH5
  | 0x65 => some .PUSH6
  | 0x66 => some .PUSH7
  | 0x67 => some .PUSH8
  | 0x68 => some .PUSH9
  | 0x69 => some .PUSH10
  | 0x6a => some .PUSH11
  | 0x6b => some .PUSH12
  | 0x6c => some .PUSH13
  | 0x6d => some .PUSH14
  | 0x6e => some .PUSH15
  | 0x6f => some .PUSH16
  | 0x70 => some .PUSH17
  | 0x71 => some .PUSH18
  | 0x72 => some .PUSH19
  | 0x73 => some .PUSH20
  | 0x74 => some .PUSH21
  | 0x75 => some .PUSH22
  | 0x76 => some .PUSH23
  | 0x77 => some .PUSH24
  | 0x78 => some .PUSH25
  | 0x79 => some .PUSH26
  | 0x7a => some .PUSH27
  | 0x7b => some .PUSH28
  | 0x7c => some .PUSH29
  | 0x7d => some .PUSH30
  | 0x7e => some .PUSH31
  | 0x7f => some .PUSH32

  | 0x80 => some .DUP1
  | 0x81 => some .DUP2
  | 0x82 => some .DUP3
  | 0x83 => some .DUP4
  | 0x84 => some .DUP5
  | 0x85 => some .DUP6
  | 0x86 => some .DUP7
  | 0x87 => some .DUP8
  | 0x88 => some .DUP9
  | 0x89 => some .DUP10
  | 0x8a => some .DUP11
  | 0x8b => some .DUP12
  | 0x8c => some .DUP13
  | 0x8d => some .DUP14
  | 0x8e => some .DUP15
  | 0x8f => some .DUP16

  | 0x90 => some .SWAP1
  | 0x91 => some .SWAP2
  | 0x92 => some .SWAP3
  | 0x93 => some .SWAP4
  | 0x94 => some .SWAP5
  | 0x95 => some .SWAP6
  | 0x96 => some .SWAP7
  | 0x97 => some .SWAP8
  | 0x98 => some .SWAP9
  | 0x99 => some .SWAP10
  | 0x9a => some .SWAP11
  | 0x9b => some .SWAP12
  | 0x9c => some .SWAP13
  | 0x9d => some .SWAP14
  | 0x9e => some .SWAP15
  | 0x9f => some .SWAP16

  | 0xa0 => some .LOG0
  | 0xa1 => some .LOG1
  | 0xa2 => some .LOG2
  | 0xa3 => some .LOG3
  | 0xa4 => some .LOG4

  | 0xf0 => some .CREATE
  | 0xf1 => some .CALL
  | 0xf2 => some .CALLCODE
  | 0xf3 => some .RETURN
  | 0xf4 => some .DELEGATECALL
  | 0xf5 => some .CREATE2
  | 0xfa => some .STATICCALL
  | 0xfd => some .REVERT
  | 0xfe => some .INVALID
  | 0xff => some .SELFDESTRUCT
  | _    => some .INVALID -- `INVALID` behaves just like any other invalid instruction

end EVM

end EvmYul

```
`EvmYul/EVM/PrecompiledContracts.lean`:

```lean
import Mathlib.Data.Nat.Log

import EvmYul.Maps.AccountMap
import EvmYul.UInt256
import EvmYul.State.Substate
import EvmYul.State.ExecutionEnv
import EvmYul.EVM.Exception
import EvmYul.Wheels

import EvmYul.EllipticCurves
import EvmYul.SHA256
import EvmYul.RIP160
import EvmYul.BN_ADD
import EvmYul.BN_MUL
import EvmYul.SNARKV
import EvmYul.BLAKE2_F
import EvmYul.PointEval

import EvmYul.FFI.ffi

open EvmYul

def Ξ_ECREC
  (σ : (AccountMap .EVM))
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 3000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let h := d.readBytes 0 32
    let v := d.readBytes 32 32
    let r := d.readBytes 64 32
    let s := d.readBytes 96 32
    let v' : ℕ := fromByteArrayBigEndian v
    let r' : ℕ := fromByteArrayBigEndian r
    let s' : ℕ := fromByteArrayBigEndian s
    let o :=
      if v' < 27 || 28 < v' || r' = 0 || r' >= secp256k1n || s' = 0 || s' >= secp256k1n then
        .empty
      else
        match ECDSARECOVER h ⟨#[.ofNat v' - 27]⟩ r s with
          | .ok s =>
              ffi.ByteArray.zeroes ⟨12⟩ ++ (ffi.KEC s).extract 12 32
          | .error e =>
            dbg_trace s!"Ξ_ECREC failed: {e}"
            .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_SHA256
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    60 + 12 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match ffi.SHA256 I.calldata with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_SHA56 failed: {e}"
          .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_RIP160
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    600 + 120 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o :=
      match RIP160 I.calldata with
        | .ok s => s
        | .error e =>
          dbg_trace s!"Ξ_RIP160 failed: {e}"
          .empty
    (true, σ, g - .ofNat gᵣ, A, o)

def Ξ_ID
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ :=
    let l := I.calldata.size
    let ceil := ( l + 31 ) / 32
    15 + 3 * ceil

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := I.calldata
    (true, σ, g - .ofNat gᵣ, A, o)

def nat_of_slice
  (B: ByteArray)
  (start: ℕ)
  (width: ℕ) : ℕ
:=
  let slice := B.readWithoutPadding start width
  let padding := width - slice.size
  fromByteArrayBigEndian slice <<< (8 * padding)

def expModAux (m : ℕ) (a : ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => a % m
  | n@(k + 1) =>
    if n % 2 == 1 then
      expModAux m (a * c % m) (c * c % m) (n / 2)
    else
      expModAux m (a % m)     (c * c % m) (n / 2)

def expMod (m : ℕ) (b : UInt256) (n : ℕ) : ℕ := expModAux m 1 b.toNat n

def Ξ_EXPMOD
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let data := I.calldata
  let base_length := nat_of_slice data 0 32
  let exp_length := nat_of_slice data 32 32
  let modulus_length := nat_of_slice data 64 32
  -- Pseudo laziness
  -- We don't want to call `nat_of_slice` unless we need it
  let exp := λ () ↦ nat_of_slice data (96 + base_length) exp_length

  let gᵣ :=
    let multiplication_complexity x y := ((max x y + 7) / 8) ^ 2
    let adjusted_exp_length :=
      if exp_length ≤ 32 && exp () == 0 then
        0
      else
        if exp_length ≤ 32 then
          Nat.log 2 (exp ())
        else
          let length_part := 8 * (exp_length - 32)
          let bits_part :=
            let exp_head := nat_of_slice data (96 + base_length) 32
            if 32 < exp_length ∧ exp_head != 0 then
              Nat.log 2 exp_head
            else
              0
          length_part + bits_part
    let iterations := max adjusted_exp_length 1
    let G_quaddivisor := 3

    max 200 (multiplication_complexity base_length modulus_length * iterations / G_quaddivisor)

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let modulus := nat_of_slice data (96 + base_length + exp_length) modulus_length
    let o : ByteArray :=
      if modulus_length == 0 || modulus == 0 then
        ffi.ByteArray.zeroes ⟨modulus_length⟩
      else
        let base := nat_of_slice data 96 base_length
        let exp := nat_of_slice data (96 + base_length) exp_length
        let expmod_base := BE (expMod modulus (.ofNat base) exp)
        let expmod_zeroes :=
          if modulus_length ≥ expmod_base.size then
            ffi.ByteArray.zeroes ⟨modulus_length - expmod_base.size⟩
          else
            ByteArray.empty
        expmod_zeroes ++ expmod_base
    (true, σ, g - .ofNat gᵣ, A, o)

private def expmodOutput :=
  let (_, _, _, _, o) :=
    Ξ_EXPMOD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv .EVM) with
        calldata := l_B ++ l_E ++ l_M ++ B ++ E ++ M
      }
  o
 where
  l_B : ByteArray := UInt256.toByteArray ⟨2⟩
  l_E : ByteArray := UInt256.toByteArray ⟨1⟩
  l_M : ByteArray := UInt256.toByteArray ⟨1⟩
  B : ByteArray := ⟨#[1, 0]⟩ -- 2^8
  E : ByteArray := ⟨#[2]⟩
  M : ByteArray := ⟨#[100]⟩

def Ξ_BN_ADD
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 150

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let y := (d.readBytes 64 32, d.readBytes 96 32)
    let o := BN_ADD x.1 x.2 y.1 y.2
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_ADD failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (false, ∅, ⟨0⟩, A, .empty)

private def bn_addOutput₀ :=
  let (_, _, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv .EVM) with
        calldata := x₁ ++ y₁ ++ x₂ ++ y₂
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨0⟩
  x₂ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₂ : ByteArray := UInt256.toByteArray ⟨2⟩

private def bn_addOutput₁ :=
  let (_, _, _, _, o) :=
    Ξ_BN_ADD
      default
      ⟨3000⟩
      default
      { (default : ExecutionEnv .EVM) with
        calldata := bn_addOutput₀ ++ x ++ y
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BN_MUL
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let gᵣ : ℕ := 6000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let d := I.calldata
    let x := (d.readBytes 0 32, d.readBytes 32 32)
    let n := d.readBytes 64 32
    let o := BN_MUL x.1 x.2 n
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BN_MUL failed: {e}"
        -- (σ, g - gᵣ, A, .empty)
        (false, ∅, ⟨0⟩, A, .empty)

private def bn_mulOutput :=
  let (_, _, _, _, o) :=
    Ξ_BN_MUL
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv .EVM) with
        calldata := x₁ ++ y₁ ++ n
      }
  o
 where
  x₁ : ByteArray := UInt256.toByteArray ⟨1⟩
  y₁ : ByteArray := UInt256.toByteArray ⟨2⟩
  n  : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_SNARKV
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let k := d.size / 192
  let gᵣ : ℕ := 34000 * k + 45000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := SNARKV d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_SNARKV failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)

private def snarkvOutput :=
  let (_, _, _, _, o) :=
    Ξ_SNARKV
      default
      ⟨100000⟩
      default
      { (default : ExecutionEnv .EVM) with
        calldata := x ++ y ++ ffi.ByteArray.zeroes ⟨32 * 4⟩
      }
  o
 where
  x : ByteArray := UInt256.toByteArray ⟨1⟩
  y : ByteArray := UInt256.toByteArray ⟨2⟩

def Ξ_BLAKE2_F
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let gᵣ : ℕ := fromByteArrayBigEndian (d.extract 0 4)

  if g.toNat < gᵣ then
    dbg_trace "failed"
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := ffi.BLAKE2 d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_BLAKE2_F failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)

def Ξ_PointEval
  (σ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  (Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
:=
  let d := I.calldata
  let gᵣ : ℕ := 50000

  if g.toNat < gᵣ then
    (false, ∅, ⟨0⟩, A, .empty)
  else
    let o := PointEval d
    match o with
      | .ok o => (true, σ, g - .ofNat gᵣ, A, o)
      | .error e =>
        dbg_trace s!"Ξ_PointEval failed: {e}"
        (false, ∅, ⟨0⟩, A, .empty)

```
`EvmYul/EVM/PrimOps.lean`:

```lean
import EvmYul.Data.Stack

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.StateOps
import EvmYul.SharedStateOps

namespace EvmYul

namespace EVM

def Transformer := EVM.State → Except EVM.ExecutionException EVM.State

def execUnOp (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.stack.pop with
      | some ⟨stack, μ₀⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀)
      | _ =>
        .error .StackUnderflow

def execBinOp (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ => Id.run do
        let result := f μ₀ μ₁
        .ok <| s.replaceStackAndIncrPC (stack.push result)
      | _ =>
        .error .StackUnderflow

def execTriOp (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂)
      | _ =>
        .error .StackUnderflow

def execQuadOp (f : Primop.Quaternary) : Transformer :=
  λ s ↦
    match s.stack.pop4 with
      | some ⟨ stack , μ₀ , μ₁ , μ₂, μ₃ ⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂ μ₃)
      | _ =>
        .error .StackUnderflow

def executionEnvOp (op : ExecutionEnv .EVM → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.executionEnv
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def unaryExecutionEnvOp (op : ExecutionEnv .EVM → UInt256 → UInt256) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop with
    | some ⟨ s , μ₀⟩ => Id.run do
      let result := op evmState.executionEnv μ₀
      .ok <|
        evmState.replaceStackAndIncrPC (s.push result)
    | _ => .error .StackUnderflow

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.toMachineState
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let mState' := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let (val, mState') := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error .StackUnderflow

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ s , μ₀, μ₁, μ₂ ⟩ => Id.run do
      let mState' := op evmState.toMachineState μ₀ μ₁ μ₂
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def binaryStateOp
  (op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let state' := op evmState.toState μ₀ μ₁
      let evmState' := {evmState with toState := state'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

def stateOp (op : EvmYul.State .EVM → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toState)

def unaryStateOp
  (op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256)
    :
  Transformer
:= λ evmState ↦
      match evmState.stack.pop with
        | some ⟨stack' , μ₀ ⟩ => Id.run do
          let (state', b) := op evmState.toState μ₀
          let evmState' := {evmState with toState := state'}
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error .StackUnderflow

def ternaryCopyOp
  (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ stack' , μ₀, μ₁, μ₂⟩ => Id.run do
      let sState' := op evmState.toSharedState μ₀ μ₁ μ₂
      let evmState' := { evmState with toSharedState := sState'}
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error .StackUnderflow

def quaternaryCopyOp
  (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    :
  Transformer
:=  λ evmState ↦
      match evmState.stack.pop4 with
        | some ⟨ stack' , μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
          let sState' := op evmState.toSharedState μ₀ μ₁ μ₂ μ₃
          let evmState' := { evmState with toSharedState := sState'}
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow

private def evmLogOp (evmState : State) (μ₀ μ₁ : UInt256) (t : Array UInt256) : State :=
  let sharedState' := SharedState.logOp μ₀ μ₁ t evmState.toSharedState
  { evmState with toSharedState := sharedState'}

def log0Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop2 with
      | some ⟨stack', μ₀, μ₁⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log1Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log2Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop4 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log3Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop5 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

def log4Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop6 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

end EVM

end EvmYul

```
`EvmYul/EVM/Semantics.lean`:

```lean
import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Semantics
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

import Conform.Wheels

open EvmYul.DebuggingAndProfiling

namespace EvmYul

namespace EVM

def argOnNBytesOfInstr : Operation .EVM → ℕ
  -- | .Push .PUSH0 => 0 is handled as default.
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def N (pc : UInt256) (instr : Operation .EVM) := pc + ⟨1⟩ + .ofNat (argOnNBytesOfInstr instr)

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt256) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let instr ← arr.get? pc.toNat >>= EvmYul.EVM.parseInstr
  let argWidth := argOnNBytesOfInstr instr
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (EvmYul.uInt256OfByteArray (arr.extract' pc.toNat.succ (pc.toNat.succ + argWidth)), argWidth)
  )

def fetchInstr (I : EvmYul.ExecutionEnv .EVM) (pc : UInt256) :
               Except EVM.ExecutionException (Operation .EVM × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .StackUnderflow) Except.ok

partial def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 :=
  match c.get? i.toNat >>= EvmYul.EVM.parseInstr with
    | none => result
    | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = .JUMPDEST then result.push i else result)

def D_J (c : ByteArray) (i : UInt256) : Array UInt256 :=
  D_J_aux c i #[]

private def BitVec.ofFn {k} (x : Fin k → Bool) : BitVec k :=
  BitVec.ofNat k (natOfBools (Vector.ofFn x))
  where natOfBools (vec : Vector Bool k) : Nat :=
          (·.1) <| vec.toList.foldl (init := (0, 0)) λ (res, i) bit ↦ (res + 2^i * bit.toNat, i + 1)

def byteAt (μ₀ μ₁ : UInt256) : UInt256 :=
  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < ⟨32⟩
                                             then v₁.getLsbD i
                                             else false)
  EvmYul.UInt256.ofNat (BitVec.toNat vᵣ)

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

mutual

def call (fuel : Nat)
  (gasCost : Nat)
  (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (evmState : State)
    :
  Except EVM.ExecutionException (UInt256 × State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := evmState.executionEnv.codeOwner
      let σ := evmState.accountMap
      let Iₑ := evmState.executionEnv.depth
      let callgas := Ccallgas t recipient value gas σ evmState.toMachineState evmState.substate
      let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let i := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
      let A' := evmState.addAccessedAccount t |>.substate
      let (cA, σ', g', A', z, o) ← do
        if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
          let resultOfΘ ←
            Θ (fuel := f)
              blobVersionedHashes
              (createdAccounts := evmState.createdAccounts)
              (genesisBlockHeader := evmState.genesisBlockHeader)
              (blocks := evmState.blocks)
              (σ  := σ)                                     -- σ in  Θ(σ, ..)
              (σ₀ := evmState.σ₀)
              (A  := A')                                    -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := evmState.executionEnv.sender)          -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute .EVM σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat evmState.executionEnv.gasPrice) -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := evmState.executionEnv.header)
              (w  := permission)                            -- I_w in Θ(.., I_W)
          pure resultOfΘ
        else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
          .ok
            (evmState.createdAccounts, evmState.toState.accountMap, .ofNat callgas, A', false, .empty)
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (.ofNat o.size)

      let μ'ₘ := writeBytes o 0 evmState.toMachineState outOffset.toNat n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      let μ'_g := μ'ₘ.gasAvailable + g' -- Ccall is subtracted in X as part of C

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.find? evmState.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
      let μ'incomplete : MachineState :=
        { μ'ₘ with
            returnData   := μ'ₒ
            gasAvailable := μ'_g
            activeWords :=
              let m : ℕ:= MachineState.M evmState.toMachineState.activeWords.toNat inOffset.toNat inSize.toNat
              .ofNat <| MachineState.M m outOffset.toNat outSize.toNat

        }

      let result : State := { evmState with accountMap := σ', substate := A', createdAccounts := cA }
      let result := {
        result with toMachineState := μ'incomplete
      }
      .ok (x, result)

def step (fuel : ℕ) (gasCost : ℕ) (instr : Option (Operation .EVM × Option (UInt256 × Nat)) := .none)
  : EVM.Transformer
:=
  match fuel with
    | 0 => λ _ ↦ .error .OutOfFuel
    | .succ f =>
    λ (evmState : EVM.State) ↦ do
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    let (instr, arg) ←
      match instr with
        | .none => fetchInstr evmState.toState.executionEnv evmState.pc
        | .some (instr, arg) => pure (instr, arg)
    let evmState := { evmState with execLength := evmState.execLength + 1 }
    match instr with
      | .CREATE =>
        let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
        match evmState.stack.pop3 with
          | some ⟨stack, μ₀, μ₁, μ₂⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

            let (a, evmState', g', z, o)
                  : (AccountAddress × EVM.State × UInt256 × Bool × ByteArray)
              :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok (a, cA, σ', g', A', z, o) =>
                    ( a
                    , { evmState with
                          accountMap := σ'
                          substate := A'
                          createdAccounts := cA
                      }
                    , g'
                    , z
                    , o
                    )
                  | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
              else
                (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L (evmState.gasAvailable.toNat) then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                  activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                  returnData := newReturnData
                  gasAvailable :=
                    .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := EvmYul.UInt256.toByteArray μ₃
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
            let (a, evmState', g', z, o) : (AccountAddress × EVM.State × UInt256 × Bool × ByteArray) :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok (a, cA, σ', g', A', z, o) =>
                    (a, {evmState with accountMap := σ', substate := A', createdAccounts := cA}, g', z, o)
                  | _ => (0, {evmState with accountMap := ∅}, ⟨0⟩, False, .empty)
              else
                (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L evmState.gasAvailable.toNat then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                returnData := newReturnData
                gasAvailable := .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .CALLCODE =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .DELEGATECALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /-μ₂,-/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STATICCALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /- μ₂, -/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | instr => EvmYul.step instr arg {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}

/--
  Iterative progression of `step`
-/
def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let I_b := evmState.toState.executionEnv.code
      let instr@(w, _) := decode I_b evmState.pc |>.getD (.STOP, .none)
      -- (159)
      let W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
        w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
        (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)
      -- Exceptional halting (158)
      let Z (evmState : State) : Except EVM.ExecutionException (State × ℕ) := do
        let cost₁ := memoryExpansionCost evmState w
        if evmState.gasAvailable.toNat < cost₁ then
          .error .OutOfGass
        let gasAvailable := evmState.gasAvailable - .ofNat cost₁
        let evmState := { evmState with gasAvailable := gasAvailable}
        let cost₂ := C' evmState w

        if evmState.gasAvailable.toNat < cost₂ then
          .error .OutOfGass

        if δ w = none then
          .error .InvalidInstruction

        if evmState.stack.length < (δ w).getD 0 then
          .error .StackUnderflow

        let invalidJump := notIn evmState.stack[0]? validJumps

        if w = .JUMP ∧ invalidJump then
          .error .BadJumpDestination

        if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
          .error .BadJumpDestination

        if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
          .error .InvalidMemoryAccess

        if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
          .error .StackOverflow

        if (¬ evmState.executionEnv.perm) ∧ W w evmState.stack then
          .error .StaticModeViolation

        if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
          .error .OutOfGass

        if
          w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
        then
          .error .OutOfGass

        pure (evmState, cost₂)
      let H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          some <| μ.H_return
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none
      match Z evmState with
        | .error e =>
          .error e
        | some (evmState, cost₂) =>
          let evmState' ← step f cost₂ instr evmState
          -- Maybe we should restructure in a way such that it is more meaningful to compute
          -- gas independently, but the model has not been set up thusly and it seems
          -- that neither really was the YP.
          -- Similarly, we cannot reach a situation in which the stack elements are not available
          -- on the stack because this is guarded above. As such, `C` can be pure here.
          match H evmState'.toMachineState w with -- The YP does this in a weird way.
            | none => X f validJumps evmState'
            | some o =>
              if w == .REVERT then
                /-
                  The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
                  but we actually have to call the semantics of `REVERT` to pass the test
                  EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
                  And the EEL spec does so too.
                -/
                .ok <| .revert evmState'.gasAvailable o
              else
                .ok <| .success evmState' o
 where
  belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
    match o with
      | none => false
      | some n => l.contains n
  notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (belongs o l)

/--
  The code execution function
-/
def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (fuel : ℕ)
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  Except
    EVM.ExecutionException
    (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let defState : EVM.State := default
      let freshEvmState : EVM.State :=
        { defState with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := createdAccounts
            gasAvailable := g
            blocks := blocks
            genesisBlockHeader := genesisBlockHeader
        }
      let result ← X f (D_J I.code ⟨0⟩) freshEvmState
      match result with
        | .success evmState' o =>
          let finalGas := evmState'.gasAvailable
          .ok (ExecutionResult.success (evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate) o)
        | .revert g' o => .ok (ExecutionResult.revert g' o)

def Lambda
  (fuel : ℕ)
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare) -- needed for EIP-6780
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)          -- available gas
  (p : UInt256)          -- gas price
  (v : UInt256)          -- endowment
  (i : ByteArray)        -- the initialisation EVM code
  (e : UInt256)          -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader)      -- "I_H has no special treatment and is determined from the blockchain"
  (w : Bool)             -- permission to make modifications to the state
  :
  Except EVM.ExecutionException
    ( AccountAddress
    × Batteries.RBSet AccountAddress compare
    × AccountMap .EVM
    × UInt256
    × Substate
    × Bool
    × ByteArray
    )
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f => do

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let n : UInt256 := (σ.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  let lₐ ← L_A s n ζ i
  let a : AccountAddress := -- (94) (95)
    (ffi.KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let existentAccount := σ.findD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (i, createdAccounts) :=
    if
      existentAccount.nonce ≠ ⟨0⟩
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, createdAccounts)
    else (i, createdAccounts.insert a)

  let newAccount : Account .EVM :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.find? s with
      | none =>  σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv .EVM :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , calldata := default
    , code      := i
    , gasPrice  := p.toNat
    , header    := H
    , depth     := e.toNat
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    }
  match Ξ f createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar exEnv with
    | .error e =>
      if e == .OutOfFuel then throw .OutOfFuel
      .ok (a, createdAccounts, σ, ⟨0⟩, AStar, false, .empty)
    | .ok (.revert g' o) =>
      .ok (a, createdAccounts, σ, g', AStar, false, o)
    | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

      let σ' : AccountMap .EVM := -- (115)
        if F then σ else
          let newAccount' := σStarStar.findD a default
          σStarStar.insert a {newAccount' with code := returnedData}

      -- (114)
      let g' := if F then 0 else gStarStar.toNat - c

      -- (116)
      let A' := if F then AStar else AStarStar
      -- (117)
      let z := not F
      .ok (a, createdAccounts', σ', .ofNat g', A', z, .empty) -- (93)
 where
  L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  := -- (96)
    let s := s.toByteArray
    let n := BE n.toNat
    match ζ with
      | none   => RLP <| .𝕃 [.𝔹 s, .𝔹 n]
      | some ζ => .some <| BE 255 ++ s ++ ζ ++ ffi.KEC i

/--
Message cal
`σ`  - evm state
`A`  - accrued substate
`s`  - sender
`o`  - transaction originator
`r`  - recipient
`c`  - the account whose code is to be called, usually the same as `r`
`g`  - available gas
`p`  - effective gas price
`v`  - value
`v'` - value in the execution context
`d`  - input data of the call
`e`  - depth of the message-call / contract-creation stack
`w`  - permissions to make modifications to the stack

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
def Θ (fuel : Nat)
      (blobVersionedHashes : List ByteArray)
      (createdAccounts : Batteries.RBSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader)
      (blocks : ProcessedBlocks)
      (σ  : AccountMap .EVM)
      (σ₀  : AccountMap .EVM)
      (A  : Substate)
      (s  : AccountAddress)
      (o  : AccountAddress)
      (r  : AccountAddress)
      (c  : ToExecute .EVM)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Nat)
      (H : BlockHeader)
      (w  : Bool)
        :
      Except EVM.ExecutionException (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => do

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != ⟨0⟩ then
          σ.insert r { (default : Account .EVM) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.find? s with
      | none => σ'₁
      | some acc =>
        σ'₁.insert s { acc with balance := acc.balance - v}

  let I : ExecutionEnv .EVM :=
    {
      codeOwner := r        -- Equation (132)
      sender    := o        -- Equation (133)
      gasPrice  := p.toNat  -- Equation (134)
      calldata := d        -- Equation (135)
      source    := s        -- Equation (136)
      weiValue  := v'       -- Equation (137)
      depth     := e        -- Equation (138)
      perm      := w        -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match c with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := H
      blobVersionedHashes := blobVersionedHashes
    }

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (createdAccounts, z, σ'', g', A'', out) ←
    match c with
      | ToExecute.Precompiled p =>
        match p with
          | 1  => .ok <| (∅, Ξ_ECREC σ₁ g A I)
          | 2  => .ok <| (∅, Ξ_SHA256 σ₁ g A I)
          | 3  => .ok <| (∅, Ξ_RIP160 σ₁ g A I)
          | 4  => .ok <| (∅, Ξ_ID σ₁ g A I)
          | 5  => .ok <| (∅, Ξ_EXPMOD σ₁ g A I)
          | 6  => .ok <| (∅, Ξ_BN_ADD σ₁ g A I)
          | 7  => .ok <| (∅, Ξ_BN_MUL σ₁ g A I)
          | 8  => .ok <| (∅, Ξ_SNARKV σ₁ g A I)
          | 9  => .ok <| (∅, Ξ_BLAKE2_F σ₁ g A I)
          | 10 => .ok <| (∅, Ξ_PointEval σ₁ g A I)
          | _ => default
      | ToExecute.Code _ =>
        match Ξ fuel createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I with
          | .error e =>
            if e == .OutOfFuel then throw .OutOfFuel
            pure (createdAccounts, false, σ, ⟨0⟩, A, .empty)
          | .ok (.revert g' o) =>
            pure (createdAccounts, false, σ, g', A, o)
          | .ok (.success (a, b, c, d) o) =>
            pure (a, true, b, c, d, o)

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (119)
  .ok (createdAccounts, σ', g', A', z, out)

end

open Batteries (RBMap RBSet)


-- Type Υ using \Upsilon or \GU
def Υ (fuel : ℕ)
  (σ : AccountMap .EVM)
  (H_f : ℕ)
  (H : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except EVM.Exception (AccountMap .EVM × Substate × Bool × UInt256)
:= do
  let g₀ : ℕ := EVM.intrinsicGas T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.find? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp}
  let createdAccounts : Batteries.RBSet AccountAddress compare := .empty
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          Lambda fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            g
            p
            T.base.value
            T.base.data
            ⟨0⟩
            none
            H
            true
        with
          | .ok (_, _, σ_P, g', A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          Θ fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            t
            (toExecute .EVM σ₀ t)
            g
            p
            T.base.value
            T.base.value
            T.base.data
            0
            H
            true
        with
          | .ok (_, σ_P, g',  A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance .EVM S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != ⟨0⟩ then
      σStar.increaseBalance .EVM H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ' -- (88)
  let σ' := σ'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty})
  .ok (σ', A, z, T.base.gasLimit - gStar)
end EVM

end EvmYul

```
`EvmYul/EVM/State.lean`:

```lean
import EvmYul.Data.Stack

import EvmYul.State
import EvmYul.SharedState

namespace EvmYul

namespace EVM

/--
The EVM `State` (extends EvmYul.SharedState).
- `pc`         `pc`
- `stack`      `s`
- `execLength` - Length of execution.
-/
structure State extends EvmYul.SharedState .EVM where
  pc    : UInt256
  stack : Stack UInt256
  execLength : ℕ
  deriving Inhabited

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)

end EVM

end EvmYul

```
`EvmYul/EVM/StateOps.lean`:

```lean
import Mathlib.Data.List.Intervals

import EvmYul.UInt256
import EvmYul.EVM.State
import EvmYul.State.AccountOps
import EvmYul.StateOps

namespace EvmYul

namespace EVM

namespace State

section Instructions

def incrPC (I : EVM.State) (pcΔ : ℕ := 1) : EVM.State :=
  { I with pc := I.pc + .ofNat pcΔ }

def replaceStackAndIncrPC (I : EVM.State) (s : Stack UInt256) (pcΔ : ℕ := 1) : EVM.State :=
  incrPC { I with stack := s } pcΔ

end Instructions

def liftMState {m} [Monad m] (f : EvmYul.State .EVM → m (EvmYul.State .EVM)) : EVM.State → m EVM.State :=
  λ s ↦ do pure { s with toState := ← f s.toState }

instance {m} [Monad m] : CoeFun (EvmYul.State .EVM → m (EvmYul.State .EVM)) (λ _ ↦ EVM.State → m EVM.State) := ⟨liftMState⟩

def liftState (f : EvmYul.State .EVM → EvmYul.State .EVM) : EVM.State → EVM.State :=
  liftMState (m := Id) f

instance : CoeFun (EvmYul.State .EVM → EvmYul.State .EVM) (λ _ ↦ EVM.State → EVM.State) := ⟨liftState⟩

def initialiseAccount (addr : AccountAddress) : EVM.State → EVM.State :=
  EvmYul.State.initialiseAccount addr

def updateAccount (addr : AccountAddress) (act : Account .EVM) : EVM.State → EVM.State :=
  EvmYul.State.updateAccount addr act

def isEmpty (self : EVM.State) : Bool := self.toState.accountMap == ∅

end State

end EVM

end EvmYul

```
`EvmYul/EllipticCurves.lean`:

```lean
-- Requires the following python packages: coincurve, typing-extensions

import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels
import EvmYul.SpongeHash.Keccak256

def secp256k1n : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337

def blobECDSARECOVER (e v r s : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput e v r s
  where pythonCommandOfInput (e v r s : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/recover.py", e, v, r, s]
  }

def blobSign (e pᵣ : String) : List String :=
  (String.split · Char.isWhitespace) ∘ totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput e pᵣ
  where pythonCommandOfInput (e pᵣ : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/sign.py", e, pᵣ]
  }

-- Appendix F. Signing Transactions

def ECDSASIGN (e pᵣ : ByteArray) : Except String (ByteArray × ByteArray × ByteArray) := do
  let [r, s, v] := blobSign (toHex e) (toHex pᵣ) | .error "error"
  let v ← ByteArray.ofBlob <| padLeft 2 v -- 2 characters means 1 byte
  let r ← ByteArray.ofBlob <| padLeft 64 r -- 64 characters means 23
  let s ← ByteArray.ofBlob <| padLeft 64 s -- 64 characters means 23
  .ok (v, r, s)

def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  match blobECDSARECOVER (toHex e) (toHex v) (toHex r) (toHex s) with
    | "error" => .error "ECDSARECOVER failed"
    | s => ByteArray.ofBlob <| padLeft 128 s /- 128 characters means 64 bytes -/

open Batteries

```
`EvmYul/EllipticCurvesPy/__init__.py`:

```py
"""
Cryptographic primitives used in Ethereum.
"""

```
`EvmYul/EllipticCurvesPy/alt_bn128.py`:

```py
"""
The alt_bn128 curve
^^^^^^^^^^^^^^^^^^^
"""

import elliptic_curve, finite_field

ALT_BN128_PRIME = 21888242871839275222246405745257275088696311157297823662689037894645226208583  # noqa: E501
ALT_BN128_CURVE_ORDER = 21888242871839275222246405745257275088548364400416034343698204186575808495617  # noqa: E501
ATE_PAIRING_COUNT = 29793968203157093289
ATE_PAIRING_COUNT_BITS = 63


class BNF(finite_field.PrimeField):
    """
    The prime field over which the alt_bn128 curve is defined.
    """

    PRIME = ALT_BN128_PRIME


class BNP(elliptic_curve.EllipticCurve):
    """
    The alt_bn128 curve.
    """

    FIELD = BNF
    A = BNF(0)
    B = BNF(3)


class BNF2(finite_field.GaloisField):
    """
    `BNF` extended with a square root of 1 (`i`).
    """

    PRIME = ALT_BN128_PRIME
    MODULUS = (1, 0)

    i: "BNF2"
    i_plus_9: "BNF2"


BNF2.FROBENIUS_COEFFICIENTS = BNF2.calculate_frobenius_coefficients()
"""autoapi_noindex"""

BNF2.i = BNF2((0, 1))
"""autoapi_noindex"""

BNF2.i_plus_9 = BNF2((9, 1))
"""autoapi_noindex"""


class BNP2(elliptic_curve.EllipticCurve):
    """
    A twist of `BNP`. This is actually the same curve as `BNP` under a change
    of variable, but that change of variable is only possible over the larger
    field `BNP12`.
    """

    FIELD = BNF2
    A = BNF2.zero()
    B = BNF2.from_int(3) / (BNF2.i + BNF2.from_int(9))


class BNF12(finite_field.GaloisField):
    """
    `BNF2` extended by adding a 6th root of `9 + i` called `w` (omega).
    """

    PRIME = ALT_BN128_PRIME
    MODULUS = (82, 0, 0, 0, 0, 0, -18, 0, 0, 0, 0, 0)

    w: "BNF12"
    i_plus_9: "BNF12"

    def __mul__(self: "BNF12", right: "BNF12") -> "BNF12":  # type: ignore[override] # noqa: E501
        """
        Multiplication special cased for BNF12.
        """
        mul = [0] * 23

        for i in range(12):
            for j in range(12):
                mul[i + j] += self[i] * right[j]

        for i in range(22, 11, -1):
            mul[i - 6] -= mul[i] * (-18)
            mul[i - 12] -= mul[i] * 82

        return BNF12.__new__(
            BNF12,
            mul[:12],
        )


BNF12.FROBENIUS_COEFFICIENTS = BNF12.calculate_frobenius_coefficients()
"""autoapi_noindex"""

BNF12.w = BNF12((0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0))
"""autoapi_noindex"""

BNF12.i_plus_9 = BNF12.w**6
"""autoapi_noindex"""


class BNP12(elliptic_curve.EllipticCurve):
    """
    The same curve as `BNP`, but defined over the larger field. This curve has
    both subgroups of order `ALT_BN128_CURVE_ORDER` and allows pairings to be
    computed.
    """

    FIELD = BNF12
    A = BNF12.zero()
    B = BNF12.from_int(3)


def bnf2_to_bnf12(x: BNF2) -> BNF12:
    """
    Lift a field element in `BNF2` to `BNF12`.
    """
    return BNF12.from_int(x[0]) + BNF12.from_int(x[1]) * (
        BNF12.i_plus_9 - BNF12.from_int(9)
    )


def bnp_to_bnp12(p: BNP) -> BNP12:
    """
    Lift a point from `BNP` to `BNP12`.
    """
    return BNP12(BNF12.from_int(int(p.x)), BNF12.from_int(int(p.y)))


def twist(p: BNP2) -> BNP12:
    """
    Apply to twist to change variables from the curve `BNP2` to `BNP12`.
    """
    return BNP12(
        bnf2_to_bnf12(p.x) * (BNF12.w**2),
        bnf2_to_bnf12(p.y) * (BNF12.w**3),
    )


def linefunc(p1: BNP12, p2: BNP12, t: BNP12) -> BNF12:
    """
    Evaluate the function defining the line between points `p1` and `p2` at the
    point `t`. The mathematical significance of this function is that is has
    divisor `(p1) + (p2) + (p1 + p2) - 3(O)`.

    Note: Abstract mathematical presentations of Miller's algorithm often
    specify the divisor `(p1) + (p2) - (p1 + p2) - (O)`. This turns out not to
    matter.
    """
    if p1.x != p2.x:
        lam = (p2.y - p1.y) / (p2.x - p1.x)
        return lam * (t.x - p1.x) - (t.y - p1.y)
    elif p1.y == p2.y:
        lam = BNF12.from_int(3) * p1.x**2 / (BNF12.from_int(2) * p1.y)
        return lam * (t.x - p1.x) - (t.y - p1.y)
    else:
        return t.x - p1.x


def miller_loop(q: BNP12, p: BNP12) -> BNF12:
    """
    The core of the pairing algorithm.
    """
    if p == BNP12.point_at_infinity() or q == BNP12.point_at_infinity():
        return BNF12.from_int(1)
    r = q
    f = BNF12.from_int(1)
    for i in range(ATE_PAIRING_COUNT_BITS, -1, -1):
        f = f * f * linefunc(r, r, p)
        r = r.double()
        if (ATE_PAIRING_COUNT - 1) & (2**i):
            f = f * linefunc(r, q, p)
            r = r + q
    assert r == q.mul_by(ATE_PAIRING_COUNT - 1)

    q1 = BNP12(q.x.frobenius(), q.y.frobenius())
    nq2 = BNP12(q1.x.frobenius(), -q1.y.frobenius())

    f = f * linefunc(r, q1, p)
    r = r + q1
    f = f * linefunc(r, nq2, p)

    return f ** ((ALT_BN128_PRIME**12 - 1) // ALT_BN128_CURVE_ORDER)


def pairing(q: BNP2, p: BNP) -> BNF12:
    """
    Compute the pairing of `q` and `p`.
    """
    return miller_loop(twist(q), bnp_to_bnp12(p))

```
`EvmYul/EllipticCurvesPy/base_types.py`:

```py
"""
Integer and array types which are used by—but not unique to—Ethereum.

[`Uint`] represents non-negative integers of arbitrary size, while subclasses
of [`FixedUint`] (like [`U256`] or [`U32`]) represent non-negative integers of
particular sizes.

Similarly, [`Bytes`] represents arbitrarily long byte sequences, while
subclasses of [`FixedBytes`] (like [`Bytes0`] or [`Bytes64`]) represent
sequences containing an exact number of bytes.

[`Uint`]: ref:ethereum.base_types.Uint
[`FixedUint`]: ref:ethereum.base_types.FixedUint
[`U32`]: ref:ethereum.base_types.U32
[`U256`]: ref:ethereum.base_types.U256
[`Bytes`]: ref:ethereum.base_types.Bytes
[`FixedBytes`]: ref:ethereum.base_types.FixedBytes
[`Bytes0`]: ref:ethereum.base_types.Bytes0
[`Bytes64`]: ref:ethereum.base_types.Bytes64
"""

from dataclasses import is_dataclass, replace
from typing import (
    Any,
    Callable,
    ClassVar,
    Optional,
    Protocol,
    Tuple,
    Type,
    TypeVar,
    runtime_checkable,
)


@runtime_checkable
class SlottedFreezable(Protocol):
    """
    A [`Protocol`] implemented by data classes annotated with
    [`@slotted_freezable`].

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    [`Protocol`]: https://docs.python.org/library/typing.html#typing.Protocol
    """

    _frozen: bool


U255_CEIL_VALUE = 2**255
"""
Smallest value that requires 256 bits to represent. Mostly used in signed
arithmetic operations, like [`sdiv`].

[`sdiv`]: ref:ethereum.frontier.vm.instructions.arithmetic.sdiv
"""

U256_CEIL_VALUE = 2**256
"""
Smallest value that requires 257 bits to represent. Used when converting a
[`U256`] in two's complement format to a regular `int` in [`U256.to_signed`].

[`U256`]: ref:ethereum.base_types.U256
[`U256.to_signed`]: ref:ethereum.base_types.U256.to_signed
"""


class Uint(int):
    """
    Unsigned integer of arbitrary size.
    """

    __slots__ = ()

    @classmethod
    def from_be_bytes(cls: Type, buffer: "Bytes") -> "Uint":
        """
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its big endian representation.
        """
        return cls(int.from_bytes(buffer, "big"))

    @classmethod
    def from_le_bytes(cls: Type, buffer: "Bytes") -> "Uint":
        """
        Converts a sequence of bytes into an arbitrarily sized unsigned integer
        from its little endian representation.
        """
        return cls(int.from_bytes(buffer, "little"))

    def __init__(self, value: int) -> None:
        if not isinstance(value, int):
            raise TypeError()

        if value < 0:
            raise OverflowError()

    def __radd__(self, left: int) -> "Uint":
        return self.__add__(left)

    def __add__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__add__(self, right))

    def __iadd__(self, right: int) -> "Uint":
        return self.__add__(right)

    def __sub__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or self < right:
            raise OverflowError()

        return int.__new__(self.__class__, int.__sub__(self, right))

    def __rsub__(self, left: int) -> "Uint":
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or self > left:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rsub__(self, left))

    def __isub__(self, right: int) -> "Uint":
        return self.__sub__(right)

    def __mul__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__mul__(self, right))

    def __rmul__(self, left: int) -> "Uint":
        return self.__mul__(left)

    def __imul__(self, right: int) -> "Uint":
        return self.__mul__(right)

    # Explicitly don't override __truediv__, __rtruediv__, and __itruediv__
    # since they return floats anyway.

    def __floordiv__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__floordiv__(self, right))

    def __rfloordiv__(self, left: int) -> "Uint":
        if not isinstance(left, int):
            return NotImplemented

        if left < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rfloordiv__(self, left))

    def __ifloordiv__(self, right: int) -> "Uint":
        return self.__floordiv__(right)

    def __mod__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__mod__(self, right))

    def __rmod__(self, left: int) -> "Uint":
        if not isinstance(left, int):
            return NotImplemented

        if left < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rmod__(self, left))

    def __imod__(self, right: int) -> "Uint":
        return self.__mod__(right)

    def __divmod__(self, right: int) -> Tuple["Uint", "Uint"]:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        result = int.__divmod__(self, right)
        return (
            int.__new__(self.__class__, result[0]),
            int.__new__(self.__class__, result[1]),
        )

    def __rdivmod__(self, left: int) -> Tuple["Uint", "Uint"]:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0:
            raise OverflowError()

        result = int.__rdivmod__(self, left)
        return (
            int.__new__(self.__class__, result[0]),
            int.__new__(self.__class__, result[1]),
        )

    def __pow__(  # type: ignore[override]
        self, right: int, modulo: Optional[int] = None
    ) -> "Uint":
        if modulo is not None:
            if not isinstance(modulo, int):
                return NotImplemented

            if modulo < 0:
                raise OverflowError()

        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__pow__(self, right, modulo))

    def __rpow__(  # type: ignore[misc]
        self, left: int, modulo: Optional[int] = None
    ) -> "Uint":
        if modulo is not None:
            if not isinstance(modulo, int):
                return NotImplemented

            if modulo < 0:
                raise OverflowError()

        if not isinstance(left, int):
            return NotImplemented

        if left < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rpow__(self, left, modulo))

    def __ipow__(  # type: ignore[override]
        self, right: int, modulo: Optional[int] = None
    ) -> "Uint":
        return self.__pow__(right, modulo)

    def __xor__(self, right: int) -> "Uint":
        if not isinstance(right, int):
            return NotImplemented

        if right < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__xor__(self, right))

    def __rxor__(self, left: int) -> "Uint":
        if not isinstance(left, int):
            return NotImplemented

        if left < 0:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rxor__(self, left))

    def __ixor__(self, right: int) -> "Uint":
        return self.__xor__(right)

    # TODO: Implement and, or, neg, pos, abs, invert, ...

    def to_be_bytes32(self) -> "Bytes32":
        """
        Converts this arbitrarily sized unsigned integer into its big endian
        representation with exactly 32 bytes.
        """
        return Bytes32(self.to_bytes(32, "big"))

    def to_be_bytes(self) -> "Bytes":
        """
        Converts this arbitrarily sized unsigned integer into its big endian
        representation, without padding.
        """
        bit_length = self.bit_length()
        byte_length = (bit_length + 7) // 8
        return self.to_bytes(byte_length, "big")

    def to_le_bytes(self, number_bytes: Optional[int] = None) -> "Bytes":
        """
        Converts this arbitrarily sized unsigned integer into its little endian
        representation, without padding.
        """
        if number_bytes is None:
            bit_length = self.bit_length()
            number_bytes = (bit_length + 7) // 8
        return self.to_bytes(number_bytes, "little")


T = TypeVar("T", bound="FixedUint")


class FixedUint(int):
    """
    Superclass for fixed size unsigned integers. Not intended to be used
    directly, but rather to be subclassed.
    """

    MAX_VALUE: ClassVar["FixedUint"]
    """
    Largest value that can be represented by this integer type.
    """

    __slots__ = ()

    def __init__(self: T, value: int) -> None:
        if not isinstance(value, int):
            raise TypeError()

        if value < 0 or value > self.MAX_VALUE:
            raise OverflowError()

    def __radd__(self: T, left: int) -> T:
        return self.__add__(left)

    def __add__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        result = int.__add__(self, right)

        if right < 0 or result > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, result)

    def wrapping_add(self: T, right: int) -> T:
        """
        Return a new instance containing `self + right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        """
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        # This is a fast way of ensuring that the result is < (2 ** 256)
        return int.__new__(
            self.__class__, int.__add__(self, right) & self.MAX_VALUE
        )

    def __iadd__(self: T, right: int) -> T:
        return self.__add__(right)

    def __sub__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE or self < right:
            raise OverflowError()

        return int.__new__(self.__class__, int.__sub__(self, right))

    def wrapping_sub(self: T, right: int) -> T:
        """
        Return a new instance containing `self - right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        """
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        # This is a fast way of ensuring that the result is < (2 ** 256)
        return int.__new__(
            self.__class__, int.__sub__(self, right) & self.MAX_VALUE
        )

    def __rsub__(self: T, left: int) -> T:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE or self > left:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rsub__(self, left))

    def __isub__(self: T, right: int) -> T:
        return self.__sub__(right)

    def __mul__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        result = int.__mul__(self, right)

        if right < 0 or result > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, result)

    def wrapping_mul(self: T, right: int) -> T:
        """
        Return a new instance containing `self * right (mod N)`.

        Passing a `right` value greater than [`MAX_VALUE`] or less than zero
        will raise a `ValueError`, even if the result would fit in this integer
        type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        """
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        # This is a fast way of ensuring that the result is < (2 ** 256)
        return int.__new__(
            self.__class__, int.__mul__(self, right) & self.MAX_VALUE
        )

    def __rmul__(self: T, left: int) -> T:
        return self.__mul__(left)

    def __imul__(self: T, right: int) -> T:
        return self.__mul__(right)

    # Explicitly don't override __truediv__, __rtruediv__, and __itruediv__
    # since they return floats anyway.

    def __floordiv__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__floordiv__(self, right))

    def __rfloordiv__(self: T, left: int) -> T:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rfloordiv__(self, left))

    def __ifloordiv__(self: T, right: int) -> T:
        return self.__floordiv__(right)

    def __mod__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__mod__(self, right))

    def __rmod__(self: T, left: int) -> T:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rmod__(self, left))

    def __imod__(self: T, right: int) -> T:
        return self.__mod__(right)

    def __divmod__(self: T, right: int) -> Tuple[T, T]:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        result = super(FixedUint, self).__divmod__(right)
        return (
            int.__new__(self.__class__, result[0]),
            int.__new__(self.__class__, result[1]),
        )

    def __rdivmod__(self: T, left: int) -> Tuple[T, T]:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE:
            raise OverflowError()

        result = super(FixedUint, self).__rdivmod__(left)
        return (
            int.__new__(self.__class__, result[0]),
            int.__new__(self.__class__, result[1]),
        )

    def __pow__(  # type: ignore[override]
        self: T, right: int, modulo: Optional[int] = None
    ) -> T:
        if modulo is not None:
            if not isinstance(modulo, int):
                return NotImplemented

            if modulo < 0 or modulo > self.MAX_VALUE:
                raise OverflowError()

        if not isinstance(right, int):
            return NotImplemented

        result = int.__pow__(self, right, modulo)

        if right < 0 or right > self.MAX_VALUE or result > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, result)

    def wrapping_pow(self: T, right: int, modulo: Optional[int] = None) -> T:
        """
        Return a new instance containing `self ** right (mod modulo)`.

        If omitted, `modulo` defaults to `Uint(self.MAX_VALUE) + 1`.

        Passing a `right` or `modulo` value greater than [`MAX_VALUE`] or
        less than zero will raise a `ValueError`, even if the result would fit
        in this integer type.

        [`MAX_VALUE`]: ref:ethereum.base_types.FixedUint.MAX_VALUE
        """
        if modulo is not None:
            if not isinstance(modulo, int):
                return NotImplemented

            if modulo < 0 or modulo > self.MAX_VALUE:
                raise OverflowError()

        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        # This is a fast way of ensuring that the result is < (2 ** 256)
        return int.__new__(
            self.__class__, int.__pow__(self, right, modulo) & self.MAX_VALUE
        )

    def __rpow__(  # type: ignore[misc]
        self: T, left: int, modulo: Optional[int] = None
    ) -> T:
        if modulo is not None:
            if not isinstance(modulo, int):
                return NotImplemented

            if modulo < 0 or modulo > self.MAX_VALUE:
                raise OverflowError()

        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rpow__(self, left, modulo))

    def __ipow__(  # type: ignore[override]
        self: T, right: int, modulo: Optional[int] = None
    ) -> T:
        return self.__pow__(right, modulo)

    def __and__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__and__(self, right))

    def __or__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__or__(self, right))

    def __xor__(self: T, right: int) -> T:
        if not isinstance(right, int):
            return NotImplemented

        if right < 0 or right > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__xor__(self, right))

    def __rxor__(self: T, left: int) -> T:
        if not isinstance(left, int):
            return NotImplemented

        if left < 0 or left > self.MAX_VALUE:
            raise OverflowError()

        return int.__new__(self.__class__, int.__rxor__(self, left))

    def __ixor__(self: T, right: int) -> T:
        return self.__xor__(right)

    def __invert__(self: T) -> T:
        return int.__new__(
            self.__class__, int.__invert__(self) & self.MAX_VALUE
        )

    def __rshift__(self: T, shift_by: int) -> T:
        if not isinstance(shift_by, int):
            return NotImplemented
        return int.__new__(self.__class__, int.__rshift__(self, shift_by))

    def to_be_bytes(self) -> "Bytes":
        """
        Converts this unsigned integer into its big endian representation,
        omitting leading zero bytes.
        """
        bit_length = self.bit_length()
        byte_length = (bit_length + 7) // 8
        return self.to_bytes(byte_length, "big")

    # TODO: Implement neg, pos, abs ...


class U256(FixedUint):
    """
    Unsigned integer, which can represent `0` to `2 ** 256 - 1`, inclusive.
    """

    MAX_VALUE: ClassVar["U256"]
    """
    Largest value that can be represented by this integer type.
    """

    __slots__ = ()

    @classmethod
    def from_be_bytes(cls: Type, buffer: "Bytes") -> "U256":
        """
        Converts a sequence of bytes into a fixed sized unsigned integer
        from its big endian representation.
        """
        if len(buffer) > 32:
            raise ValueError()

        return cls(int.from_bytes(buffer, "big"))

    @classmethod
    def from_signed(cls: Type, value: int) -> "U256":
        """
        Creates an unsigned integer representing `value` using two's
        complement.
        """
        if value >= 0:
            return cls(value)

        return cls(value & cls.MAX_VALUE)

    def to_be_bytes32(self) -> "Bytes32":
        """
        Converts this 256-bit unsigned integer into its big endian
        representation with exactly 32 bytes.
        """
        return Bytes32(self.to_bytes(32, "big"))

    def to_signed(self) -> int:
        """
        Decodes a signed integer from its two's complement representation.
        """
        if self.bit_length() < 256:
            # This means that the sign bit is 0
            return int(self)

        # -1 * (2's complement of U256 value)
        return int(self) - U256_CEIL_VALUE


U256.MAX_VALUE = int.__new__(U256, (2**256) - 1)

B = TypeVar("B", bound="FixedBytes")


class FixedBytes(bytes):
    """
    Superclass for fixed sized byte arrays. Not intended to be used directly,
    but should be subclassed.
    """

    LENGTH: int
    """
    Number of bytes in each instance of this class.
    """

    __slots__ = ()

    def __new__(cls: Type[B], *args: Any, **kwargs: Any) -> B:
        """
        Create a new instance, ensuring the result has the correct length.
        """
        result = super(FixedBytes, cls).__new__(cls, *args, **kwargs)
        if len(result) != cls.LENGTH:
            raise ValueError(
                f"expected {cls.LENGTH} bytes but got {len(result)}"
            )
        return result


class Bytes0(FixedBytes):
    """
    Byte array of exactly zero elements.
    """

    LENGTH = 0
    """
    Number of bytes in each instance of this class.
    """


class Bytes4(FixedBytes):
    """
    Byte array of exactly four elements.
    """

    LENGTH = 4
    """
    Number of bytes in each instance of this class.
    """


class Bytes8(FixedBytes):
    """
    Byte array of exactly eight elements.
    """

    LENGTH = 8
    """
    Number of bytes in each instance of this class.
    """


class Bytes20(FixedBytes):
    """
    Byte array of exactly 20 elements.
    """

    LENGTH = 20
    """
    Number of bytes in each instance of this class.
    """


class Bytes32(FixedBytes):
    """
    Byte array of exactly 32 elements.
    """

    LENGTH = 32
    """
    Number of bytes in each instance of this class.
    """


class Bytes48(FixedBytes):
    """
    Byte array of exactly 48 elements.
    """

    LENGTH = 48

class Bytes96(FixedBytes):
    """
    Byte array of exactly 96 elements.
    """

    LENGTH = 96


class Bytes64(FixedBytes):
    """
    Byte array of exactly 64 elements.
    """

    LENGTH = 64
    """
    Number of bytes in each instance of this class.
    """


class Bytes256(FixedBytes):
    """
    Byte array of exactly 256 elements.
    """

    LENGTH = 256
    """
    Number of bytes in each instance of this class.
    """


Bytes = bytes
"""
Sequence of bytes (octets) of arbitrary length.
"""


def _setattr_function(self: Any, attr: str, value: Any) -> None:
    if getattr(self, "_frozen", None):
        raise Exception("Mutating frozen dataclasses is not allowed.")
    else:
        object.__setattr__(self, attr, value)


def _delattr_function(self: Any, attr: str) -> None:
    if self._frozen:
        raise Exception("Mutating frozen dataclasses is not allowed.")
    else:
        object.__delattr__(self, attr)


def _make_init_function(f: Callable) -> Callable:
    def init_function(self: Any, *args: Any, **kwargs: Any) -> None:
        will_be_frozen = kwargs.pop("_frozen", True)
        object.__setattr__(self, "_frozen", False)
        f(self, *args, **kwargs)
        self._frozen = will_be_frozen

    return init_function


def slotted_freezable(cls: Any) -> Any:
    """
    Monkey patches a dataclass so it can be frozen by setting `_frozen` to
    `True` and uses `__slots__` for efficiency.

    Instances will be created frozen by default unless you pass `_frozen=False`
    to `__init__`.
    """
    cls.__slots__ = ("_frozen",) + tuple(cls.__annotations__)
    cls.__init__ = _make_init_function(cls.__init__)
    cls.__setattr__ = _setattr_function
    cls.__delattr__ = _delattr_function
    return type(cls)(cls.__name__, cls.__bases__, dict(cls.__dict__))


S = TypeVar("S")


def modify(obj: S, f: Callable[[S], None]) -> S:
    """
    Create a copy of `obj` (which must be [`@slotted_freezable`]), and modify
    it by applying `f`. The returned copy will be frozen.

    [`@slotted_freezable`]: ref:ethereum.base_types.slotted_freezable
    """
    assert is_dataclass(obj)
    assert isinstance(obj, SlottedFreezable)
    new_obj = replace(obj, _frozen=False)
    f(new_obj)
    new_obj._frozen = True
    return new_obj

```
`EvmYul/EllipticCurvesPy/blake2.py`:

```py
"""
The Blake2 Implementation
^^^^^^^^^^^^^^^^^^^^^^^^^^
"""
import struct
from dataclasses import dataclass
from typing import List, Tuple

from base_types import Uint


def spit_le_to_uint(data: bytes, start: int, num_words: int) -> List[Uint]:
    """
    Extracts 8 byte words from a given data.

    Parameters
    ----------
    data :
        The data in bytes from which the words need to be extracted
    start :
        Position to start the extraction
    num_words:
        The number of words to be extracted
    """
    words = []
    for i in range(num_words):
        start_position = start + (i * 8)
        words.append(
            Uint.from_le_bytes(data[start_position : start_position + 8])
        )

    return words


@dataclass
class Blake2:
    """
    Implementation of the BLAKE2 cryptographic hashing algorithm.

    Please refer the following document for details:
    https://datatracker.ietf.org/doc/html/rfc7693
    """

    w: int
    mask_bits: int
    word_format: str

    R1: int
    R2: int
    R3: int
    R4: int

    @property
    def max_word(self) -> int:
        """
        Largest value for a given Blake2 flavor.
        """
        return 2**self.w

    @property
    def w_R1(self) -> int:
        """
        (w - R1) value for a given Blake2 flavor.
        Used in the function G
        """
        return self.w - self.R1

    @property
    def w_R2(self) -> int:
        """
        (w - R2) value for a given Blake2 flavor.
        Used in the function G
        """
        return self.w - self.R2

    @property
    def w_R3(self) -> int:
        """
        (w - R3) value for a given Blake2 flavor.
        Used in the function G
        """
        return self.w - self.R3

    @property
    def w_R4(self) -> int:
        """
        (w - R4) value for a given Blake2 flavor.
        Used in the function G
        """
        return self.w - self.R4

    sigma: Tuple = (
        (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15),
        (14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3),
        (11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4),
        (7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8),
        (9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13),
        (2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9),
        (12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11),
        (13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10),
        (6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5),
        (10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0),
    )

    IV: Tuple = (
        0x6A09E667F3BCC908,
        0xBB67AE8584CAA73B,
        0x3C6EF372FE94F82B,
        0xA54FF53A5F1D36F1,
        0x510E527FADE682D1,
        0x9B05688C2B3E6C1F,
        0x1F83D9ABFB41BD6B,
        0x5BE0CD19137E2179,
    )

    @property
    def sigma_len(self) -> int:
        """
        Length of the sigma parameter.
        """
        return len(self.sigma)

    def get_blake2_parameters(self, data: bytes) -> Tuple:
        """
        Extract the parameters required in the Blake2 compression function
        from the provided bytes data.

        Parameters
        ----------
        data :
            The bytes data that has been passed in the message.
        """
        rounds = Uint.from_be_bytes(data[:4])
        h = spit_le_to_uint(data, 4, 8)
        m = spit_le_to_uint(data, 68, 16)
        t_0, t_1 = spit_le_to_uint(data, 196, 2)
        f = Uint.from_be_bytes(data[212:])

        return (rounds, h, m, t_0, t_1, f)

    def G(
        self, v: List, a: int, b: int, c: int, d: int, x: int, y: int
    ) -> List:
        """
        The mixing function used in Blake2
        https://datatracker.ietf.org/doc/html/rfc7693#section-3.1

        Parameters
        ----------
        v :
            The working vector to be mixed.
        a, b, c, d :
            Indexes within v of the words to be mixed.
        x, y :
            The two input words for the mixing.
        """
        v[a] = (v[a] + v[b] + x) % self.max_word
        v[d] = ((v[d] ^ v[a]) >> self.R1) ^ (
            (v[d] ^ v[a]) << self.w_R1
        ) % self.max_word

        v[c] = (v[c] + v[d]) % self.max_word
        v[b] = ((v[b] ^ v[c]) >> self.R2) ^ (
            (v[b] ^ v[c]) << self.w_R2
        ) % self.max_word

        v[a] = (v[a] + v[b] + y) % self.max_word
        v[d] = ((v[d] ^ v[a]) >> self.R3) ^ (
            (v[d] ^ v[a]) << self.w_R3
        ) % self.max_word

        v[c] = (v[c] + v[d]) % self.max_word
        v[b] = ((v[b] ^ v[c]) >> self.R4) ^ (
            (v[b] ^ v[c]) << self.w_R4
        ) % self.max_word

        return v

    def compress(
        self,
        num_rounds: Uint,
        h: List[Uint],
        m: List[Uint],
        t_0: Uint,
        t_1: Uint,
        f: bool,
    ) -> bytes:
        """
        'F Compression' from section 3.2 of RFC 7693:
        https://tools.ietf.org/html/rfc7693#section-3.2

        Parameters
        ----------
        num_rounds :
            The number of rounds. A 32-bit unsigned big-endian word
        h :
            The state vector. 8 unsigned 64-bit little-endian words
        m :
            The message block vector. 16 unsigned 64-bit little-endian words
        t_0, t_1 :
            Offset counters. 2 unsigned 64-bit little-endian words
        f:
            The final block indicator flag. An 8-bit word
        """
        # Initialize local work vector v[0..15]
        v = [0] * 16
        v[0:8] = h  # First half from state
        v[8:15] = self.IV  # Second half from IV

        v[12] = t_0 ^ self.IV[4]  # Low word of the offset
        v[13] = t_1 ^ self.IV[5]  # High word of the offset

        if f:
            v[14] = v[14] ^ self.mask_bits  # Invert all bits for last block

        # Mixing
        for r in range(num_rounds):
            # for more than sigma_len rounds, the schedule
            # wraps around to the beginning
            s = self.sigma[r % self.sigma_len]

            v = self.G(v, 0, 4, 8, 12, m[s[0]], m[s[1]])
            v = self.G(v, 1, 5, 9, 13, m[s[2]], m[s[3]])
            v = self.G(v, 2, 6, 10, 14, m[s[4]], m[s[5]])
            v = self.G(v, 3, 7, 11, 15, m[s[6]], m[s[7]])
            v = self.G(v, 0, 5, 10, 15, m[s[8]], m[s[9]])
            v = self.G(v, 1, 6, 11, 12, m[s[10]], m[s[11]])
            v = self.G(v, 2, 7, 8, 13, m[s[12]], m[s[13]])
            v = self.G(v, 3, 4, 9, 14, m[s[14]], m[s[15]])

        result_message_words = (h[i] ^ v[i] ^ v[i + 8] for i in range(8))
        return struct.pack("<8%s" % self.word_format, *result_message_words)


# Parameters specific to the Blake2b implementation
@dataclass
class Blake2b(Blake2):
    """
    The Blake2b flavor (64-bits) of Blake2.
    This version is used in the pre-compiled contract.
    """

    w: int = 64
    mask_bits: int = 0xFFFFFFFFFFFFFFFF
    word_format: str = "Q"

    R1: int = 32
    R2: int = 24
    R3: int = 16
    R4: int = 63

```
`EvmYul/EllipticCurvesPy/blake2_f.py`:

```py
import sys
from base_types import U256, Uint
from alt_bn128 import (
    ALT_BN128_CURVE_ORDER,
    ALT_BN128_PRIME,
    BNF,
    BNF2,
    BNF12,
    BNP,
    BNP2,
    pairing,
)
from blake2 import Blake2b

data = bytes.fromhex(sys.argv[1])
if len(data) != 213:
    print('error', end = '')
    sys.exit()

blake2b = Blake2b()
rounds, h, m, t_0, t_1, f = blake2b.get_blake2_parameters(data)

if f not in [0, 1]:
    print('error', end = '')
    sys.exit()

output = blake2b.compress(rounds, h, m, t_0, t_1, f)
print(bytes.hex(output), end = '')

```
`EvmYul/EllipticCurvesPy/bn_add.py`:

```py
import sys
from base_types import U256, Uint
from alt_bn128 import (
    ALT_BN128_CURVE_ORDER,
    ALT_BN128_PRIME,
    BNF,
    BNF2,
    BNF12,
    BNP,
    BNP2,
    pairing,
)

# OPERATION
x0_bytes = bytes.fromhex(sys.argv[1])
x0_value = U256.from_be_bytes(x0_bytes)
y0_bytes = bytes.fromhex(sys.argv[2])
y0_value = U256.from_be_bytes(y0_bytes)
x1_bytes = bytes.fromhex(sys.argv[3])
x1_value = U256.from_be_bytes(x1_bytes)
y1_bytes = bytes.fromhex(sys.argv[4])
y1_value = U256.from_be_bytes(y1_bytes)

for i in (x0_value, y0_value, x1_value, y1_value):
    if i >= ALT_BN128_PRIME:
        print('error', end = '')
        sys.exit()


try:
    p0 = BNP(BNF(x0_value), BNF(y0_value))
    p1 = BNP(BNF(x1_value), BNF(y1_value))
except ValueError:
    print('error', end = '')
    sys.exit()

p = p0 + p1

output = p.x.to_be_bytes32() + p.y.to_be_bytes32()
print(bytes.hex(output), end = '')
```
`EvmYul/EllipticCurvesPy/bn_mul.py`:

```py
import sys
from base_types import U256, Uint
from alt_bn128 import (
    ALT_BN128_CURVE_ORDER,
    ALT_BN128_PRIME,
    BNF,
    BNF2,
    BNF12,
    BNP,
    BNP2,
    pairing,
)

# OPERATION
x0_bytes = bytes.fromhex(sys.argv[1])
x0_value = U256.from_be_bytes(x0_bytes)
y0_bytes = bytes.fromhex(sys.argv[2])
y0_value = U256.from_be_bytes(y0_bytes)
n = U256.from_be_bytes(bytes.fromhex(sys.argv[3]))

for i in (x0_value, y0_value):
    if i >= ALT_BN128_PRIME:
        print('error', end = '')
        sys.exit()

try:
    p0 = BNP(BNF(x0_value), BNF(y0_value))
except ValueError:
    print('error', end = '')
    sys.exit()

p = p0.mul_by(n)

output = p.x.to_be_bytes32() + p.y.to_be_bytes32()
print(bytes.hex(output), end = '')

```
`EvmYul/EllipticCurvesPy/elliptic_curve.py`:

```py
"""
Elliptic Curves
^^^^^^^^^^^^^^^
"""

from typing import Generic, Type, TypeVar

import coincurve

from base_types import U256, Bytes
from finite_field import Field
from hash import Hash32

SECP256K1N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

F = TypeVar("F", bound=Field)
T = TypeVar("T", bound="EllipticCurve")

def secp256k1_recover(r: U256, s: U256, v: U256, msg_hash: Hash32) -> Bytes:
    """
    Recovers the public key from a given signature.

    Parameters
    ----------
    r :
        TODO
    s :
        TODO
    v :
        TODO
    msg_hash :
        Hash of the message being recovered.

    Returns
    -------
    public_key : `ethereum.base_types.Bytes`
        Recovered public key.
    """
    r_bytes = r.to_be_bytes32()
    s_bytes = s.to_be_bytes32()

    signature = bytearray([0] * 65)
    signature[32 - len(r_bytes) : 32] = r_bytes
    signature[64 - len(s_bytes) : 64] = s_bytes
    signature[64] = v
    public_key = coincurve.PublicKey.from_signature_and_message(
        bytes(signature), msg_hash, hasher=None
    )
    public_key = public_key.format(compressed=False)[1:]
    return public_key

class EllipticCurve(Generic[F]):
    """
    Superclass for integers modulo a prime. Not intended to be used
    directly, but rather to be subclassed.
    """

    __slots__ = ("x", "y")

    FIELD: Type[F]
    A: F
    B: F

    x: F
    y: F

    def __new__(cls: Type[T], x: F, y: F) -> T:
        """
        Make new point on the curve. The point is not checked to see if it is
        on the curve.
        """
        res = object.__new__(cls)
        res.x = x
        res.y = y
        return res

    def __init__(self, x: F, y: F) -> None:
        """
        Checks if the point is on the curve. To skip this check call
        `__new__()` directly.
        """
        if (
            x != self.FIELD.zero() or y != self.FIELD.zero()
        ) and y ** 2 - x**3 - self.A * x - self.B != self.FIELD.zero():
            raise ValueError("Point not on curve")

    def __eq__(self, other: object) -> bool:
        """
        Test two points for equality.
        """
        if not isinstance(other, type(self)):
            return False
        return self.x == other.x and self.y == other.y

    def __str__(self) -> str:
        """
        Stringify a point as its coordinates.
        """
        return str((self.x, self.y))

    @classmethod
    def point_at_infinity(cls: Type[T]) -> T:
        """
        Return the point at infinity. This is the identity element of the group
        operation.

        The point at infinity doesn't actually have coordinates so we use
        `(0, 0)` (which isn't on the curve) to represent it.
        """
        return cls.__new__(cls, cls.FIELD.zero(), cls.FIELD.zero())

    def double(self: T) -> T:
        """
        Add a point to itself.
        """
        x, y, F = self.x, self.y, self.FIELD
        if x == 0 and y == 0:
            return self
        lam = (F.from_int(3) * x**2 + self.A) / (F.from_int(2) * y)
        new_x = lam**2 - x - x
        new_y = lam * (x - new_x) - y
        return self.__new__(type(self), new_x, new_y)

    def __add__(self: T, other: T) -> T:
        """
        Add two points together.
        """
        ZERO = self.FIELD.zero()
        self_x, self_y, other_x, other_y = self.x, self.y, other.x, other.y
        if self_x == ZERO and self_y == ZERO:
            return other
        if other_x == ZERO and other_y == ZERO:
            return self
        if self_x == other_x:
            if self_y == other_y:
                return self.double()
            else:
                return self.point_at_infinity()
        lam = (other_y - self_y) / (other_x - self_x)
        x = lam**2 - self_x - other_x
        y = lam * (self_x - x) - self_y
        return self.__new__(type(self), x, y)

    def mul_by(self: T, n: int) -> T:
        """
        Multiply `self` by `n` using the double and add algorithm.
        """
        res = self.__new__(type(self), self.FIELD.zero(), self.FIELD.zero())
        s = self
        while n != 0:
            if n % 2 == 1:
                res = res + s
            s = s + s
            n //= 2
        return res

```
`EvmYul/EllipticCurvesPy/exceptions.py`:

```py
"""
Error types common across all Ethereum forks.
"""


class EthereumException(Exception):
    """
    Base class for all exceptions _expected_ to be thrown during normal
    operation.
    """


class InvalidBlock(EthereumException):
    """
    Thrown when a block being processed is found to be invalid.
    """


class RLPDecodingError(InvalidBlock):
    """
    Indicates that RLP decoding failed.
    """


class RLPEncodingError(EthereumException):
    """
    Indicates that RLP encoding failed.
    """

```
`EvmYul/EllipticCurvesPy/finite_field.py`:

```py
"""
Finite Fields
^^^^^^^^^^^^^
"""

# flake8: noqa: D102, D105

from typing import Iterable, List, Tuple, Type, TypeVar, cast

from typing_extensions import Protocol

from base_types import Bytes, Bytes32

F = TypeVar("F", bound="Field")


class Field(Protocol):
    """
    A type protocol for defining fields.
    """

    __slots__ = ()

    @classmethod
    def zero(cls: Type[F]) -> F:
        ...

    @classmethod
    def from_int(cls: Type[F], n: int) -> F:
        ...

    def __radd__(self: F, left: F) -> F:
        ...

    def __add__(self: F, right: F) -> F:
        ...

    def __iadd__(self: F, right: F) -> F:
        ...

    def __sub__(self: F, right: F) -> F:
        ...

    def __rsub__(self: F, left: F) -> F:
        ...

    def __mul__(self: F, right: F) -> F:
        ...

    def __rmul__(self: F, left: F) -> F:
        ...

    def __imul__(self: F, right: F) -> F:
        ...

    def __pow__(self: F, exponent: int) -> F:
        ...

    def __ipow__(self: F, right: int) -> F:
        ...

    def __neg__(self: F) -> F:
        ...

    def __truediv__(self: F, right: F) -> F:
        ...


T = TypeVar("T", bound="PrimeField")


class PrimeField(int, Field):
    """
    Superclass for integers modulo a prime. Not intended to be used
    directly, but rather to be subclassed.
    """

    __slots__ = ()
    PRIME: int

    @classmethod
    def from_be_bytes(cls: Type[T], buffer: "Bytes") -> T:
        """
        Converts a sequence of bytes into a element of the field.
        Parameters
        ----------
        buffer :
            Bytes to decode.
        Returns
        -------
        self : `T`
            Unsigned integer decoded from `buffer`.
        """
        return cls(int.from_bytes(buffer, "big"))

    @classmethod
    def zero(cls: Type[T]) -> T:
        return cls.__new__(cls, 0)

    @classmethod
    def from_int(cls: Type[T], n: int) -> T:
        return cls(n)

    def __new__(cls: Type[T], value: int) -> T:
        return int.__new__(cls, value % cls.PRIME)

    def __radd__(self: T, left: T) -> T:  # type: ignore[override]
        return self.__add__(left)

    def __add__(self: T, right: T) -> T:  # type: ignore[override]
        if not isinstance(right, int):
            return NotImplemented

        return self.__new__(type(self), int.__add__(self, right))

    def __iadd__(self: T, right: T) -> T:  # type: ignore[override]
        return self.__add__(right)

    def __sub__(self: T, right: T) -> T:  # type: ignore[override]
        if not isinstance(right, int):
            return NotImplemented

        return self.__new__(type(self), int.__sub__(self, right))

    def __rsub__(self: T, left: T) -> T:  # type: ignore[override]
        if not isinstance(left, int):
            return NotImplemented

        return self.__new__(type(self), int.__rsub__(self, left))

    def __mul__(self: T, right: T) -> T:  # type: ignore[override]
        if not isinstance(right, int):
            return NotImplemented

        return self.__new__(type(self), int.__mul__(self, right))

    def __rmul__(self: T, left: T) -> T:  # type: ignore[override]
        return self.__mul__(left)

    def __imul__(self: T, right: T) -> T:  # type: ignore[override]
        return self.__mul__(right)

    __floordiv__ = None  # type: ignore
    __rfloordiv__ = None  # type: ignore
    __ifloordiv__ = None
    __divmod__ = None  # type: ignore
    __rdivmod__ = None  # type: ignore

    def __pow__(self: T, exponent: int) -> T:  # type: ignore[override]
        # For reasons that are unclear, self must be cast to int here under
        # PyPy.
        return self.__new__(
            type(self), int.__pow__(int(self), exponent, self.PRIME)
        )

    __rpow__ = None  # type: ignore

    def __ipow__(self: T, right: int) -> T:  # type: ignore[override]
        return self.__pow__(right)

    __and__ = None  # type: ignore
    __or__ = None  # type: ignore
    __xor__ = None  # type: ignore
    __rxor__ = None  # type: ignore
    __ixor__ = None
    __rshift__ = None  # type: ignore
    __lshift__ = None  # type: ignore
    __irshift__ = None
    __ilshift__ = None

    def __neg__(self: T) -> T:
        return self.__new__(type(self), int.__neg__(self))

    def __truediv__(self: T, right: T) -> T:  # type: ignore[override]
        return self * right.multiplicative_inverse()

    def multiplicative_inverse(self: T) -> T:
        return self ** (-1)

    def to_be_bytes32(self) -> "Bytes32":
        """
        Converts this arbitrarily sized unsigned integer into its big endian
        representation with exactly 32 bytes.
        Returns
        -------
        big_endian : `Bytes32`
            Big endian (most significant bits first) representation.
        """
        return Bytes32(self.to_bytes(32, "big"))


U = TypeVar("U", bound="GaloisField")


class GaloisField(tuple, Field):
    """
    Superclass for defining finite fields. Not intended to be used
    directly, but rather to be subclassed.

    Fields are represented as `F_p[x]/(x^n + ...)` where the `MODULUS` is a
    tuple of the non-leading coefficients of the defining polynomial. For
    example `x^3 + 2x^2 + 3x + 4` is `(2, 3, 4)`.

    In practice the polynomial is likely to be sparse and you should overload
    the `__mul__()` function to take advantage of this fact.
    """

    __slots__ = ()

    PRIME: int
    MODULUS: Tuple[int, ...]
    FROBENIUS_COEFFICIENTS: Tuple["GaloisField", ...]

    @classmethod
    def zero(cls: Type[U]) -> U:
        return cls.__new__(cls, [0] * len(cls.MODULUS))

    @classmethod
    def from_int(cls: Type[U], n: int) -> U:
        return cls.__new__(cls, [n] + [0] * (len(cls.MODULUS) - 1))

    def __new__(cls: Type[U], iterable: Iterable[int]) -> U:
        self = tuple.__new__(cls, (x % cls.PRIME for x in iterable))
        assert len(self) == len(cls.MODULUS)
        return self

    def __add__(self: U, right: U) -> U:  # type: ignore[override]
        if not isinstance(right, type(self)):
            return NotImplemented

        return self.__new__(
            type(self),
            (
                x + y
                for (x, y) in cast(Iterable[Tuple[int, int]], zip(self, right))
            ),
        )

    def __radd__(self: U, left: U) -> U:
        return self.__add__(left)

    def __iadd__(self: U, right: U) -> U:  # type: ignore[override]
        return self.__add__(right)

    def __sub__(self: U, right: U) -> U:
        if not isinstance(right, type(self)):
            return NotImplemented

        x: int
        y: int
        return self.__new__(
            type(self),
            (
                x - y
                for (x, y) in cast(Iterable[Tuple[int, int]], zip(self, right))
            ),
        )

    def __rsub__(self: U, left: U) -> U:
        if not isinstance(left, type(self)):
            return NotImplemented

        return self.__new__(
            type(self),
            (
                x - y
                for (x, y) in cast(Iterable[Tuple[int, int]], zip(left, self))
            ),
        )

    def __mul__(self: U, right: U) -> U:  # type: ignore[override]
        modulus = self.MODULUS
        degree = len(modulus)
        prime = self.PRIME
        mul = [0] * (degree * 2)

        for i in range(degree):
            for j in range(degree):
                mul[i + j] += self[i] * right[j]

        for i in range(degree * 2 - 1, degree - 1, -1):
            for j in range(i - degree, i):
                mul[j] -= (mul[i] * modulus[degree - (i - j)]) % prime

        return self.__new__(
            type(self),
            mul[:degree],
        )

    def __rmul__(self: U, left: U) -> U:  # type: ignore[override]
        return self.__mul__(left)

    def __imul__(self: U, right: U) -> U:  # type: ignore[override]
        return self.__mul__(right)

    def __truediv__(self: U, right: U) -> U:
        return self * right.multiplicative_inverse()

    def __neg__(self: U) -> U:
        return self.__new__(type(self), (-a for a in self))

    def scalar_mul(self: U, x: int) -> U:
        """
        Multiply a field element by a integer. This is faster than using
        `from_int()` and field multiplication.
        """
        return self.__new__(type(self), (x * n for n in self))

    def deg(self: U) -> int:
        """
        This is a support function for `multiplicative_inverse()`.
        """
        for i in range(len(self.MODULUS) - 1, -1, -1):
            if self[i] != 0:
                return i
        raise ValueError("deg() does not support zero")

    def multiplicative_inverse(self: U) -> U:
        """
        Calculate the multiplicative inverse. Uses the Euclidean algorithm.
        """
        x2: List[int]
        p = self.PRIME
        x1, f1 = list(self.MODULUS), [0] * len(self)
        x2, f2, d2 = list(self), [1] + [0] * (len(self) - 1), self.deg()
        q_0 = pow(x2[d2], -1, p)
        for i in range(d2):
            x1[i + len(x1) - d2] = (x1[i + len(x1) - d2] - q_0 * x2[i]) % p
            f1[i + len(x1) - d2] = (f1[i + len(x1) - d2] - q_0 * f2[i]) % p
        for i in range(len(self.MODULUS) - 1, -1, -1):
            if x1[i] != 0:
                d1 = i
                break
        while True:
            if d1 == 0:
                ans = f1
                q = pow(x1[0], -1, self.PRIME)
                for i in range(len(ans)):
                    ans[i] *= q
                break
            elif d2 == 0:
                ans = f2
                q = pow(x2[0], -1, self.PRIME)
                for i in range(len(ans)):
                    ans *= q
                break
            if d1 < d2:
                q = x2[d2] * pow(x1[d1], -1, self.PRIME)
                for i in range(len(self.MODULUS) - (d2 - d1)):
                    x2[i + (d2 - d1)] = (x2[i + (d2 - d1)] - q * x1[i]) % p
                    f2[i + (d2 - d1)] = (f2[i + (d2 - d1)] - q * f1[i]) % p
                while x2[d2] == 0:
                    d2 -= 1
            else:
                q = x1[d1] * pow(x2[d2], -1, self.PRIME)
                for i in range(len(self.MODULUS) - (d1 - d2)):
                    x1[i + (d1 - d2)] = (x1[i + (d1 - d2)] - q * x2[i]) % p
                    f1[i + (d1 - d2)] = (f1[i + (d1 - d2)] - q * f2[i]) % p
                while x1[d1] == 0:
                    d1 -= 1
        return self.__new__(type(self), ans)

    def __pow__(self: U, exponent: int) -> U:
        degree = len(self.MODULUS)
        if exponent < 0:
            self = self.multiplicative_inverse()
            exponent = -exponent

        res = self.__new__(type(self), [1] + [0] * (degree - 1))
        s = self
        while exponent != 0:
            if exponent % 2 == 1:
                res *= s
            s *= s
            exponent //= 2
        return res

    def __ipow__(self: U, right: int) -> U:
        return self.__pow__(right)

    @classmethod
    def calculate_frobenius_coefficients(cls: Type[U]) -> Tuple[U, ...]:
        """
        Calculate the coefficients needed by `frobenius()`.
        """
        coefficients = []
        for i in range(len(cls.MODULUS)):
            x = [0] * len(cls.MODULUS)
            x[i] = 1
            coefficients.append(cls.__new__(cls, x) ** cls.PRIME)
        return tuple(coefficients)

    def frobenius(self: U) -> U:
        """
        Returns `self ** p`. This function is known as the Frobenius
        endomorphism and has many special mathematical properties. In
        particular it is extremely cheap to compute compared to other
        exponentiations.
        """
        ans = self.from_int(0)
        a: int
        for i, a in enumerate(self):
            ans += cast(U, self.FROBENIUS_COEFFICIENTS[i]).scalar_mul(a)
        return ans

```
`EvmYul/EllipticCurvesPy/hash.py`:

```py
from Crypto.Hash import keccak
from base_types import Bytes, Bytes32, Bytes64

Hash32 = Bytes32
Hash64 = Bytes64

def keccak256(buffer: Bytes) -> Hash32:
    """
    Computes the keccak256 hash of the input `buffer`.

    Parameters
    ----------
    buffer :
        Input for the hashing function.

    Returns
    -------
    hash : `ethereum.base_types.Hash32`
        Output of the hash function.
    """
    k = keccak.new(digest_bits=256)
    return Hash32(k.update(buffer).digest())


def keccak512(buffer: Bytes) -> Hash64:
    """
    Computes the keccak512 hash of the input `buffer`.

    Parameters
    ----------
    buffer :
        Input for the hashing function.

    Returns
    -------
    hash : `ethereum.base_types.Hash32`
        Output of the hash function.
    """
    k = keccak.new(digest_bits=512)
    return Hash64(k.update(buffer).digest())
```
`EvmYul/EllipticCurvesPy/keccak.py`:

```py
from hash import keccak256
from base_types import Bytes
import sys

fileName : Bytes = sys.argv[1]
f = open(fileName, "r")
data = bytes.fromhex(f.read())
r = keccak256(data)
print(bytes.hex(r), end = '')    
f.close()

```
`EvmYul/EllipticCurvesPy/kzg.py`:

```py
"""
The KZG Implementation
^^^^^^^^^^^^^^^^^^^^^^
"""
from hashlib import sha256
from typing import Tuple

from eth_typing.bls import BLSPubkey, BLSSignature
from base_types import Bytes, Bytes32, Bytes48, Bytes96, U256
from py_ecc.bls import G2ProofOfPossession
from py_ecc.bls.g2_primitives import pubkey_to_G1, signature_to_G2
from py_ecc.fields import optimized_bls12_381_FQ, optimized_bls12_381_FQ2
from py_ecc.fields import optimized_bls12_381_FQ12 as FQ12
from py_ecc.optimized_bls12_381 import add, multiply, neg
from py_ecc.optimized_bls12_381.optimized_curve import G1, G2
from py_ecc.optimized_bls12_381.optimized_pairing import (
    final_exponentiate,
    pairing,
)

def has_hex_prefix(hex_string: str) -> bool:
    """
    Check if a hex string starts with hex prefix (0x).

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be checked for presence of prefix.

    Returns
    -------
    has_prefix : `bool`
        Boolean indicating whether the hex string has 0x prefix.
    """
    return hex_string.startswith("0x")
    
def remove_hex_prefix(hex_string: str) -> str:
    """
    Remove 0x prefix from a hex string if present. This function returns the
    passed hex string if it isn't prefixed with 0x.

    Parameters
    ----------
    hex_string :
        The hexadecimal string whose prefix is to be removed.

    Returns
    -------
    modified_hex_string : `str`
        The hexadecimal string with the 0x prefix removed if present.
    """
    if has_hex_prefix(hex_string):
        return hex_string[len("0x") :]

    return hex_string

def hex_to_bytes(hex_string: str) -> Bytes:
    """
    Convert hex string to bytes.

    Parameters
    ----------
    hex_string :
        The hexadecimal string to be converted to bytes.

    Returns
    -------
    byte_stream : `bytes`
        Byte stream corresponding to the given hexadecimal string.
    """
    return bytes.fromhex(remove_hex_prefix(hex_string))

FQ = Tuple[
    optimized_bls12_381_FQ, optimized_bls12_381_FQ, optimized_bls12_381_FQ
]
FQ2 = Tuple[
    optimized_bls12_381_FQ2, optimized_bls12_381_FQ2, optimized_bls12_381_FQ2
]


class KZGCommitment(Bytes48):
    """KZG commitment to a polynomial."""

    pass


class KZGProof(Bytes48):
    """KZG proof"""

    pass


class BLSFieldElement(U256):
    """A field element in the BLS12-381 field."""

    pass


class VersionedHash(Bytes32):
    """A versioned hash."""

    pass


class G2Point(Bytes96):
    """A point in G2."""

    pass


VERSIONED_HASH_VERSION_KZG = hex_to_bytes("0x01")
BYTES_PER_COMMITMENT = 48
BYTES_PER_PROOF = 48
BYTES_PER_FIELD_ELEMENT = 32
G1_POINT_AT_INFINITY = b"\xc0" + b"\x00" * 47
BLS_MODULUS = BLSFieldElement(
    52435875175126190479447740508185965837690552500527637822603658699938581184513  # noqa: E501
)
KZG_SETUP_G2_LENGTH = 65
KZG_SETUP_G2_MONOMIAL_1 = "0xb5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2"  # noqa: E501


def kzg_commitment_to_versioned_hash(
    kzg_commitment: KZGCommitment,
) -> VersionedHash:
    """
    Convert a KZG commitment to a versioned hash.
    """
    return VersionedHash(
        VERSIONED_HASH_VERSION_KZG
        + Bytes32(sha256(kzg_commitment).digest())[1:]
    )


def validate_kzg_g1(b: Bytes48) -> None:
    """
    Perform BLS validation required by the types `KZGProof`
    and `KZGCommitment`.
    """
    if b == G1_POINT_AT_INFINITY:
        return

    assert G2ProofOfPossession.KeyValidate(BLSPubkey(b))


def bytes_to_kzg_commitment(b: Bytes48) -> KZGCommitment:
    """
    Convert untrusted bytes into a trusted and validated KZGCommitment.
    """
    validate_kzg_g1(b)
    return KZGCommitment(b)


def bytes_to_bls_field(b: Bytes32) -> BLSFieldElement:
    """
    Convert untrusted bytes to a trusted and validated BLS scalar
    field element. This function does not accept inputs greater than
    the BLS modulus.
    """
    field_element = int.from_bytes(b, "big")
    assert field_element < int(BLS_MODULUS)
    return BLSFieldElement(field_element)


def bytes_to_kzg_proof(b: Bytes48) -> KZGProof:
    """
    Convert untrusted bytes into a trusted and validated KZGProof.
    """
    validate_kzg_g1(b)
    return KZGProof(b)


def pairing_check(values: Tuple[Tuple[FQ, FQ2], Tuple[FQ, FQ2]]) -> bool:
    """
    Check if the pairings are valid.
    """
    p_q_1, p_q_2 = values
    final_exponentiation = final_exponentiate(
        pairing(p_q_1[1], p_q_1[0], final_exponentiate=False)
        * pairing(p_q_2[1], p_q_2[0], final_exponentiate=False)
    )
    return final_exponentiation == FQ12.one()


def verify_kzg_proof(
    commitment_bytes: Bytes48,
    z_bytes: Bytes32,
    y_bytes: Bytes32,
    proof_bytes: Bytes48,
) -> bool:
    """
    Verify KZG proof that ``p(z) == y`` where ``p(z)``
    is the polynomial represented by ``polynomial_kzg``.
    Receives inputs as bytes.
    Public method.
    """
    assert len(commitment_bytes) == BYTES_PER_COMMITMENT
    assert len(z_bytes) == BYTES_PER_FIELD_ELEMENT
    assert len(y_bytes) == BYTES_PER_FIELD_ELEMENT
    assert len(proof_bytes) == BYTES_PER_PROOF

    return verify_kzg_proof_impl(
        bytes_to_kzg_commitment(commitment_bytes),
        bytes_to_bls_field(z_bytes),
        bytes_to_bls_field(y_bytes),
        bytes_to_kzg_proof(proof_bytes),
    )


def verify_kzg_proof_impl(
    commitment: KZGCommitment,
    z: BLSFieldElement,
    y: BLSFieldElement,
    proof: KZGProof,
) -> bool:
    """
    Verify KZG proof that ``p(z) == y`` where ``p(z)``
    is the polynomial represented by ``polynomial_kzg``.
    """
    # Verify: P - y = Q * (X - z)
    X_minus_z = add(
        signature_to_G2(BLSSignature(hex_to_bytes(KZG_SETUP_G2_MONOMIAL_1))),
        multiply(G2, int((BLS_MODULUS - z) % BLS_MODULUS)),
    )
    P_minus_y = add(
        pubkey_to_G1(BLSPubkey(commitment)),
        multiply(G1, int((BLS_MODULUS - y) % BLS_MODULUS)),
    )
    return pairing_check(
        (
            (P_minus_y, neg(G2)),
            (pubkey_to_G1(BLSPubkey(proof)), X_minus_z),
        )
    )

```
`EvmYul/EllipticCurvesPy/point_evaluation.py`:

```py
import sys
"""
Ethereum Virtual Machine (EVM) POINT EVALUATION PRECOMPILED CONTRACT
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Implementation of the POINT EVALUATION precompiled contract.
"""
from base_types import Bytes, Bytes32, Bytes48, U256

from kzg import (
    KZGCommitment,
    kzg_commitment_to_versioned_hash,
    verify_kzg_proof,
)

FIELD_ELEMENTS_PER_BLOB = 4096
BLS_MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513  # noqa: E501
VERSIONED_HASH_VERSION_KZG = b"\x01"


data = bytes.fromhex(sys.argv[1])

if len(data) != 192:
    print('error', end = '')
    sys.exit()

versioned_hash = data[:32]
z = Bytes32(data[32:64])
y = Bytes32(data[64:96])
commitment = KZGCommitment(data[96:144])
proof = Bytes48(data[144:192])

if kzg_commitment_to_versioned_hash(commitment) != versioned_hash:
    print('error', end = '')
    sys.exit()

# Verify KZG proof with z and y in big endian format
try:
    kzg_proof_verification = verify_kzg_proof(commitment, z, y, proof)
except Exception as e:
    print('error', end = '')
    sys.exit()

if not kzg_proof_verification:
    print('error', end = '')
    sys.exit()

# Return FIELD_ELEMENTS_PER_BLOB and BLS_MODULUS as padded
# 32 byte big endian values
result = Bytes(
    U256(FIELD_ELEMENTS_PER_BLOB).to_be_bytes32()
    + U256(BLS_MODULUS).to_be_bytes32()
)

print(bytes.hex(result), end = '')
```
`EvmYul/EllipticCurvesPy/previous_trie.py`:

```py
"""
State Trie
^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The state trie is the structure responsible for storing
`.fork_types.Account` objects.
"""

# import copy
from typing import Any
from dataclasses import dataclass, field
from typing import (
    Callable,
    Dict,
    Generic,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
    TypeVar,
    Union,
    cast,
)

from base_types import U256, Bytes, Bytes20, Uint, slotted_freezable
from hash import Hash32

RLP = Any
Address = Bytes20
Root = Hash32
Node = Union[Bytes, Uint, U256, None]

K = TypeVar("K", bound=Bytes)
V = TypeVar(
    "V",
    # Optional[Account],
    Optional[Bytes],
    Bytes,
    # Optional[Transaction],
    # Optional[Receipt],
    # Uint,
    # U256,
)


@slotted_freezable
@dataclass
class LeafNode:
    """Leaf node in the Merkle Trie"""

    rest_of_key: Bytes
    value: RLP


@slotted_freezable
@dataclass
class ExtensionNode:
    """Extension node in the Merkle Trie"""

    key_segment: Bytes
    subnode: RLP


@slotted_freezable
@dataclass
class BranchNode:
    """Branch node in the Merkle Trie"""

    subnodes: List[RLP]
    value: RLP


InternalNode = Union[LeafNode, ExtensionNode, BranchNode]


def encode_internal_node(node: Optional[InternalNode]) -> RLP:
    """
    Encodes a Merkle Trie node into its RLP form. The RLP will then be
    serialized into a `Bytes` and hashed unless it is less that 32 bytes
    when serialized.

    This function also accepts `None`, representing the absence of a node,
    which is encoded to `b""`.

    Parameters
    ----------
    node : Optional[InternalNode]
        The node to encode.

    Returns
    -------
    encoded : `RLP`
        The node encoded as RLP.
    """
    unencoded: RLP
    if node is None:
        unencoded = b""
    elif isinstance(node, LeafNode):
        unencoded = (
            nibble_list_to_compact(node.rest_of_key, True),
            node.value,
        )
    elif isinstance(node, ExtensionNode):
        unencoded = (
            nibble_list_to_compact(node.key_segment, False),
            node.subnode,
        )
    elif isinstance(node, BranchNode):
        unencoded = node.subnodes + [node.value]
    else:
        raise AssertionError(f"Invalid internal node type {type(node)}!")

    encoded = rlp.encode(unencoded)
    if len(encoded) < 32:
        return unencoded
    else:
        return keccak256(encoded)


def encode_node(node: Node, storage_root: Optional[Bytes] = None) -> Bytes:
    """
    Encode a Node for storage in the Merkle Trie.

    Currently mostly an unimplemented stub.
    """
    if isinstance(node, Account):
        assert storage_root is not None
        return encode_account(node, storage_root)
    elif isinstance(node, (Transaction, Receipt, U256)):
        return rlp.encode(cast(RLP, node))
    elif isinstance(node, Bytes):
        return node
    else:
        raise AssertionError(
            f"encoding for {type(node)} is not currently implemented"
        )


@dataclass
class Trie(Generic[K, V]):
    """
    The Merkle Trie.
    """

    secured: bool
    default: V
    _data: Dict[K, V] = field(default_factory=dict)

def trie_set(trie: Trie[K, V], key: K, value: V) -> None:
    """
    Stores an item in a Merkle Trie.

    This method deletes the key if `value == trie.default`, because the Merkle
    Trie represents the default value by omitting it from the trie.

    Parameters
    ----------
    trie: `Trie`
        Trie to store in.
    key : `Bytes`
        Key to lookup.
    value : `V`
        Node to insert at `key`.
    """
    if value == trie.default:
        if key in trie._data:
            del trie._data[key]
    else:
        trie._data[key] = value

def common_prefix_length(a: Sequence, b: Sequence) -> int:
    """
    Find the longest common prefix of two sequences.
    """
    for i in range(len(a)):
        if i >= len(b) or a[i] != b[i]:
            return i
    return len(a)


def nibble_list_to_compact(x: Bytes, is_leaf: bool) -> Bytes:
    """
    Compresses nibble-list into a standard byte array with a flag.

    A nibble-list is a list of byte values no greater than `15`. The flag is
    encoded in high nibble of the highest byte. The flag nibble can be broken
    down into two two-bit flags.

    Highest nibble::

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0


    The lowest bit of the nibble encodes the parity of the length of the
    remaining nibbles -- `0` when even and `1` when odd. The second lowest bit
    is used to distinguish leaf and extension nodes. The other two bits are not
    used.

    Parameters
    ----------
    x :
        Array of nibbles.
    is_leaf :
        True if this is part of a leaf node, or false if it is an extension
        node.

    Returns
    -------
    compressed : `bytearray`
        Compact byte array.
    """
    compact = bytearray()

    if len(x) % 2 == 0:  # ie even length
        compact.append(16 * (2 * is_leaf))
        for i in range(0, len(x), 2):
            compact.append(16 * x[i] + x[i + 1])
    else:
        compact.append(16 * ((2 * is_leaf) + 1) + x[0])
        for i in range(1, len(x), 2):
            compact.append(16 * x[i] + x[i + 1])

    return Bytes(compact)


def bytes_to_nibble_list(bytes_: Bytes) -> Bytes:
    """
    Converts a `Bytes` into to a sequence of nibbles (bytes with value < 16).

    Parameters
    ----------
    bytes_:
        The `Bytes` to convert.

    Returns
    -------
    nibble_list : `Bytes`
        The `Bytes` in nibble-list format.
    """
    nibble_list = bytearray(2 * len(bytes_))
    for byte_index, byte in enumerate(bytes_):
        nibble_list[byte_index * 2] = (byte & 0xF0) >> 4
        nibble_list[byte_index * 2 + 1] = byte & 0x0F
    return Bytes(nibble_list)


def _prepare_trie(
    trie: Trie[K, V],
    get_storage_root: Optional[Callable[[Address], Root]] = None,
) -> Mapping[Bytes, Bytes]:
    """
    Prepares the trie for root calculation. Removes values that are empty,
    hashes the keys (if `secured == True`) and encodes all the nodes.

    Parameters
    ----------
    trie :
        The `Trie` to prepare.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.

    Returns
    -------
    out : `Mapping[ethereum.base_types.Bytes, Node]`
        Object with keys mapped to nibble-byte form.
    """
    mapped: MutableMapping[Bytes, Bytes] = {}

    for preimage, value in trie._data.items():
        if isinstance(value, Account):
            assert get_storage_root is not None
            address = Address(preimage)
            encoded_value = encode_node(value, get_storage_root(address))
        else:
            encoded_value = encode_node(value)
        if encoded_value == b"":
            raise AssertionError
        key: Bytes
        if trie.secured:
            # "secure" tries hash keys once before construction
            key = keccak256(preimage)
        else:
            key = preimage
        mapped[bytes_to_nibble_list(key)] = encoded_value

    return mapped


def root(
    trie: Trie[K, V],
    get_storage_root: Optional[Callable[[Address], Root]] = None,
) -> Root:
    """
    Computes the root of a modified merkle patricia trie (MPT).

    Parameters
    ----------
    trie :
        `Trie` to get the root of.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.


    Returns
    -------
    root : `.fork_types.Root`
        MPT root of the underlying key-value pairs.
    """
    obj = _prepare_trie(trie, get_storage_root)

    root_node = encode_internal_node(patricialize(obj, Uint(0)))
    if len(rlp.encode(root_node)) < 32:
        return keccak256(rlp.encode(root_node))
    else:
        assert isinstance(root_node, Bytes)
        return Root(root_node)


def patricialize(
    obj: Mapping[Bytes, Bytes], level: Uint
) -> Optional[InternalNode]:
    """
    Structural composition function.

    Used to recursively patricialize and merkleize a dictionary. Includes
    memoization of the tree structure and hashes.

    Parameters
    ----------
    obj :
        Underlying trie key-value pairs, with keys in nibble-list format.
    level :
        Current trie level.

    Returns
    -------
    node : `ethereum.base_types.Bytes`
        Root node of `obj`.
    """
    if len(obj) == 0:
        return None

    arbitrary_key = next(iter(obj))

    # if leaf node
    if len(obj) == 1:
        leaf = LeafNode(arbitrary_key[level:], obj[arbitrary_key])
        return leaf

    # prepare for extension node check by finding max j such that all keys in
    # obj have the same key[i:j]
    substring = arbitrary_key[level:]
    prefix_length = len(substring)
    for key in obj:
        prefix_length = min(
            prefix_length, common_prefix_length(substring, key[level:])
        )

        # finished searching, found another key at the current level
        if prefix_length == 0:
            break

    # if extension node
    if prefix_length > 0:
        prefix = arbitrary_key[level : level + prefix_length]
        return ExtensionNode(
            prefix,
            encode_internal_node(patricialize(obj, level + prefix_length)),
        )

    branches: List[MutableMapping[Bytes, Bytes]] = []
    for _ in range(16):
        branches.append({})
    value = b""
    for key in obj:
        if len(key) == level:
            # shouldn't ever have an account or receipt in an internal node
            if isinstance(obj[key], (Account, Receipt, Uint)):
                raise AssertionError
            value = obj[key]
        else:
            branches[key[level]][key] = obj[key]

    return BranchNode(
        [
            encode_internal_node(patricialize(branches[k], level + 1))
            for k in range(16)
        ],
        value,
    )

```
`EvmYul/EllipticCurvesPy/recover.py`:

```py
# requires: coincurve, pycryptodome, typing-extensions

# The order of arguments mirrors the yellow paper:
# ECDSARECOVER(e ∈ B_32, v ∈ B_1, r ∈ B_32, s ∈ B_32) ≡ pu ∈ B64
# where e is the hash of the transaction
import sys

from elliptic_curve import secp256k1_recover
from base_types import Bytes32, U256, Uint
from hash import Hash32

msg_hash : Hash32 = bytes.fromhex(sys.argv[1])

v : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[2]), "big")
r : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[3]), "big")
s : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[4]), "big")

try:
    sender = secp256k1_recover(r, s, v, msg_hash)
    print(bytes.hex(sender), end = '')
except ValueError:
    # unable to extract public key
    print('error', end = '')



```
`EvmYul/EllipticCurvesPy/rip160.py`:

```py
import sys
import hashlib
import ctypes
ctypes.CDLL("libssl.so").OSSL_PROVIDER_load(None, b"legacy")

from base_types import Bytes

def left_pad_zero_bytes(value: Bytes, size: int) -> Bytes:
    """
    Left pad zeroes to `value` if it's length is less than the given `size`.

    Parameters
    ----------
    value :
        The byte string that needs to be padded.
    size :
        The number of bytes that need that need to be padded.

    Returns
    -------
    left_padded_value: `ethereum.base_types.Bytes`
        left padded byte string of given `size`.
    """
    return value.rjust(size, b"\x00")

data = bytes.fromhex(sys.argv[1])
hash_bytes = hashlib.new("ripemd160", data).digest()
padded_hash = left_pad_zero_bytes(hash_bytes, 32)
output = padded_hash
print(bytes.hex(output), end = '')

```
`EvmYul/EllipticCurvesPy/rlp.py`:

```py
"""
.. _rlp:

Recursive Length Prefix (RLP) Encoding
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

Defines the serialization and deserialization format used throughout Ethereum.
"""

from typing import Any, Sequence
from hash import Hash32, keccak256
from exceptions import RLPEncodingError
from base_types import Bytes, FixedUint, Uint

RLP = Any


#
# RLP Encode
#


def encode(raw_data: RLP) -> Bytes:
    """
    Encodes `raw_data` into a sequence of bytes using RLP.

    Parameters
    ----------
    raw_data :
        A `Bytes`, `Uint`, `Uint256` or sequence of `RLP` encodable
        objects.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_data`.
    """
    if isinstance(raw_data, (bytearray, bytes)):
        return encode_bytes(raw_data)
    elif isinstance(raw_data, (Uint, FixedUint)):
        return encode(raw_data.to_be_bytes())
    elif isinstance(raw_data, str):
        return encode_bytes(raw_data.encode())
    elif isinstance(raw_data, bool):
        if raw_data:
            return encode_bytes(b"\x01")
        else:
            return encode_bytes(b"")
    elif isinstance(raw_data, Sequence):
        return encode_sequence(raw_data)
    elif is_dataclass(raw_data):
        return encode(astuple(raw_data))
    else:
        raise RLPEncodingError(
            "RLP Encoding of type {} is not supported".format(type(raw_data))
        )


def encode_bytes(raw_bytes: Bytes) -> Bytes:
    """
    Encodes `raw_bytes`, a sequence of bytes, using RLP.

    Parameters
    ----------
    raw_bytes :
        Bytes to encode with RLP.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_bytes`.
    """
    len_raw_data = Uint(len(raw_bytes))

    if len_raw_data == 1 and raw_bytes[0] < 0x80:
        return raw_bytes
    elif len_raw_data < 0x38:
        return bytes([0x80 + len_raw_data]) + raw_bytes
    else:
        # length of raw data represented as big endian bytes
        len_raw_data_as_be = len_raw_data.to_be_bytes()
        return (
            bytes([0xB7 + len(len_raw_data_as_be)])
            + len_raw_data_as_be
            + raw_bytes
        )


def encode_sequence(raw_sequence: Sequence[RLP]) -> Bytes:
    """
    Encodes a list of RLP encodable objects (`raw_sequence`) using RLP.

    Parameters
    ----------
    raw_sequence :
            Sequence of RLP encodable objects.

    Returns
    -------
    encoded : `ethereum.base_types.Bytes`
        The RLP encoded bytes representing `raw_sequence`.
    """
    joined_encodings = get_joined_encodings(raw_sequence)
    len_joined_encodings = Uint(len(joined_encodings))

    if len_joined_encodings < 0x38:
        return Bytes([0xC0 + len_joined_encodings]) + joined_encodings
    else:
        len_joined_encodings_as_be = len_joined_encodings.to_be_bytes()
        return (
            Bytes([0xF7 + len(len_joined_encodings_as_be)])
            + len_joined_encodings_as_be
            + joined_encodings
        )


def get_joined_encodings(raw_sequence: Sequence[RLP]) -> Bytes:
    """
    Obtain concatenation of rlp encoding for each item in the sequence
    raw_sequence.

    Parameters
    ----------
    raw_sequence :
        Sequence to encode with RLP.

    Returns
    -------
    joined_encodings : `ethereum.base_types.Bytes`
        The concatenated RLP encoded bytes for each item in sequence
        raw_sequence.
    """
    return b"".join(encode(item) for item in raw_sequence)

def rlp_hash(data: RLP) -> Hash32:
    """
    Obtain the keccak-256 hash of the rlp encoding of the passed in data.

    Parameters
    ----------
    data :
        The data for which we need the rlp hash.

    Returns
    -------
    hash : `Hash32`
        The rlp hash of the passed in data.
    """
    return keccak256(encode(data))

```
`EvmYul/EllipticCurvesPy/sha256.py`:

```py
import sys
import hashlib

data = bytes.fromhex(sys.argv[1])
output = hashlib.sha256(data).digest()
print(bytes.hex(output), end = '')

```
`EvmYul/EllipticCurvesPy/sign.py`:

```py
from typing import Tuple
from hash import Hash32
from base_types import Bytes32, U256, Uint
import sys
import coincurve

def secp256k1_sign(msg_hash: Hash32, secret_key: int) -> Tuple[U256, ...]:
    """
    Returns the signature of a message hash given the secret key.
    """
    private_key = coincurve.PrivateKey.from_int(secret_key)
    signature = private_key.sign_recoverable(msg_hash, hasher=None)

    return (
        U256.from_be_bytes(signature[0:32]),
        U256.from_be_bytes(signature[32:64]),
        U256(signature[64]),
    )

msg_hash : Hash32 = bytes.fromhex(sys.argv[1])

pr : U256 = Uint.from_bytes(bytes.fromhex(sys.argv[2]), "big")

res = secp256k1_sign(msg_hash, pr)

print(hex(res[0])[2:]) # r
print(hex(res[1])[2:]) # s
print(hex(res[2])[2:], end = '') # v

```
`EvmYul/EllipticCurvesPy/snarkv.py`:

```py
import sys
from base_types import U256, Uint
from alt_bn128 import (
    ALT_BN128_CURVE_ORDER,
    ALT_BN128_PRIME,
    BNF,
    BNF2,
    BNF12,
    BNP,
    BNP2,
    pairing,
)

data = bytes.fromhex(sys.argv[1])

# OPERATION
if len(data) % 192 != 0:
    print('error', end = '')
    sys.exit()
result = BNF12.from_int(1)
for i in range(len(data) // 192):
    values = []
    for j in range(6):
        value = U256.from_be_bytes(
            data[i * 192 + 32 * j : i * 192 + 32 * (j + 1)]
        )
        if value >= ALT_BN128_PRIME:
            print('error', end = '')
            sys.exit()
        values.append(int(value))

    try:
        p = BNP(BNF(values[0]), BNF(values[1]))
        q = BNP2(
            BNF2((values[3], values[2])), BNF2((values[5], values[4]))
        )
    except ValueError:
        print('error', end = '')
        sys.exit()

    if p.mul_by(ALT_BN128_CURVE_ORDER) != BNP.point_at_infinity():
        print('error', end = '')
        sys.exit()
    if q.mul_by(ALT_BN128_CURVE_ORDER) != BNP2.point_at_infinity():
        print('error', end = '')
        sys.exit()
    if p != BNP.point_at_infinity() and q != BNP2.point_at_infinity():
        result = result * pairing(q, p)

if result == BNF12.from_int(1):
    output = U256(1).to_be_bytes32()
else:
    output = U256(0).to_be_bytes32()

print(bytes.hex(output), end = '')

```
`EvmYul/EllipticCurvesPy/trie.py`:

```py
"""
State Trie
^^^^^^^^^^

.. contents:: Table of Contents
    :backlinks: none
    :local:

Introduction
------------

The state trie is the structure responsible for storing
`.fork_types.Account` objects.
"""

import copy
from dataclasses import dataclass, field
from typing import (
    Callable,
    Dict,
    Generic,
    List,
    Mapping,
    MutableMapping,
    Optional,
    Sequence,
    TypeVar,
    Union,
    cast,
)
import sys
import previous_trie as previous_trie
from typing import Any
from hash import Hash32
import rlp
from hash import keccak256
from base_types import U256, Bytes, Bytes20, Uint, slotted_freezable
RLP = Any
Address = Bytes20
Root = Hash32
Node = Union[
    Bytes, None
]
K = TypeVar("K", bound=Bytes)
V = TypeVar(
    "V",
    Optional[Bytes],
    Bytes,
)


@slotted_freezable
@dataclass
class LeafNode:
    """Leaf node in the Merkle Trie"""

    rest_of_key: Bytes
    value: RLP


@slotted_freezable
@dataclass
class ExtensionNode:
    """Extension node in the Merkle Trie"""

    key_segment: Bytes
    subnode: RLP


@slotted_freezable
@dataclass
class BranchNode:
    """Branch node in the Merkle Trie"""

    subnodes: List[RLP]
    value: RLP


InternalNode = Union[LeafNode, ExtensionNode, BranchNode]


def encode_internal_node(node: Optional[InternalNode]) -> RLP:
    """
    Encodes a Merkle Trie node into its RLP form. The RLP will then be
    serialized into a `Bytes` and hashed unless it is less that 32 bytes
    when serialized.

    This function also accepts `None`, representing the absence of a node,
    which is encoded to `b""`.

    Parameters
    ----------
    node : Optional[InternalNode]
        The node to encode.

    Returns
    -------
    encoded : `RLP`
        The node encoded as RLP.
    """
    unencoded: RLP
    if node is None:
        unencoded = b""
    elif isinstance(node, LeafNode):
        unencoded = (
            nibble_list_to_compact(node.rest_of_key, True),
            node.value,
        )
    elif isinstance(node, ExtensionNode):
        unencoded = (
            nibble_list_to_compact(node.key_segment, False),
            node.subnode,
        )
    elif isinstance(node, BranchNode):
        unencoded = node.subnodes + [node.value]
    else:
        raise AssertionError(f"Invalid internal node type {type(node)}!")

    encoded = rlp.encode(unencoded)
    if len(encoded) < 32:
        return unencoded
    else:
        return keccak256(encoded)


def encode_node(node: Node, storage_root: Optional[Bytes] = None) -> Bytes:
    """
    Encode a Node for storage in the Merkle Trie.

    Currently mostly an unimplemented stub.
    """
    # if isinstance(node, Account):
    #     assert storage_root is not None
    #     return encode_account(node, storage_root)
    # if isinstance(node, (LegacyTransaction, Receipt, Withdrawal, U256)):
    #     return rlp.encode(cast(RLP, node))
    if isinstance(node, Bytes):
        return node
    else:
        return previous_trie.encode_node(node, storage_root)


@dataclass
class Trie(Generic[K, V]):
    """
    The Merkle Trie.
    """

    secured: bool
    default: V
    _data: Dict[K, V] = field(default_factory=dict)

def trie_set(trie: Trie[K, V], key: K, value: V) -> None:
    """
    Stores an item in a Merkle Trie.

    This method deletes the key if `value == trie.default`, because the Merkle
    Trie represents the default value by omitting it from the trie.

    Parameters
    ----------
    trie: `Trie`
        Trie to store in.
    key : `Bytes`
        Key to lookup.
    value : `V`
        Node to insert at `key`.
    """
    if value == trie.default:
        if key in trie._data:
            del trie._data[key]
    else:
        trie._data[key] = value

def common_prefix_length(a: Sequence, b: Sequence) -> int:
    """
    Find the longest common prefix of two sequences.
    """
    for i in range(len(a)):
        if i >= len(b) or a[i] != b[i]:
            return i
    return len(a)


def nibble_list_to_compact(x: Bytes, is_leaf: bool) -> Bytes:
    """
    Compresses nibble-list into a standard byte array with a flag.

    A nibble-list is a list of byte values no greater than `15`. The flag is
    encoded in high nibble of the highest byte. The flag nibble can be broken
    down into two two-bit flags.

    Highest nibble::

        +---+---+----------+--------+
        | _ | _ | is_leaf | parity |
        +---+---+----------+--------+
          3   2      1         0


    The lowest bit of the nibble encodes the parity of the length of the
    remaining nibbles -- `0` when even and `1` when odd. The second lowest bit
    is used to distinguish leaf and extension nodes. The other two bits are not
    used.

    Parameters
    ----------
    x :
        Array of nibbles.
    is_leaf :
        True if this is part of a leaf node, or false if it is an extension
        node.

    Returns
    -------
    compressed : `bytearray`
        Compact byte array.
    """
    compact = bytearray()

    if len(x) % 2 == 0:  # ie even length
        compact.append(16 * (2 * is_leaf))
        for i in range(0, len(x), 2):
            compact.append(16 * x[i] + x[i + 1])
    else:
        compact.append(16 * ((2 * is_leaf) + 1) + x[0])
        for i in range(1, len(x), 2):
            compact.append(16 * x[i] + x[i + 1])

    return Bytes(compact)


def bytes_to_nibble_list(bytes_: Bytes) -> Bytes:
    """
    Converts a `Bytes` into to a sequence of nibbles (bytes with value < 16).

    Parameters
    ----------
    bytes_:
        The `Bytes` to convert.

    Returns
    -------
    nibble_list : `Bytes`
        The `Bytes` in nibble-list format.
    """
    nibble_list = bytearray(2 * len(bytes_))
    for byte_index, byte in enumerate(bytes_):
        nibble_list[byte_index * 2] = (byte & 0xF0) >> 4
        nibble_list[byte_index * 2 + 1] = byte & 0x0F
    return Bytes(nibble_list)


def _prepare_trie(
    trie: Trie[K, V],
    get_storage_root: Optional[Callable[[Address], Root]] = None,
) -> Mapping[Bytes, Bytes]:
    """
    Prepares the trie for root calculation. Removes values that are empty,
    hashes the keys (if `secured == True`) and encodes all the nodes.

    Parameters
    ----------
    trie :
        The `Trie` to prepare.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.

    Returns
    -------
    out : `Mapping[ethereum.base_types.Bytes, Node]`
        Object with keys mapped to nibble-byte form.
    """
    mapped: MutableMapping[Bytes, Bytes] = {}

    for preimage, value in trie._data.items():
        # if isinstance(value, Account):
        #     assert get_storage_root is not None
        #     address = Address(preimage)
        #     encoded_value = encode_node(value, get_storage_root(address))
        # else:
        encoded_value = encode_node(value)
        if encoded_value == b"":
            raise AssertionError
        key: Bytes
        if trie.secured:
            # "secure" tries hash keys once before construction
            key = keccak256(preimage)
        else:
            key = preimage
        mapped[bytes_to_nibble_list(key)] = encoded_value

    return mapped


def root(
    trie: Trie[K, V],
    get_storage_root: Optional[Callable[[Address], Root]] = None,
) -> Root:
    """
    Computes the root of a modified merkle patricia trie (MPT).

    Parameters
    ----------
    trie :
        `Trie` to get the root of.
    get_storage_root :
        Function to get the storage root of an account. Needed to encode
        `Account` objects.


    Returns
    -------
    root : `.fork_types.Root`
        MPT root of the underlying key-value pairs.
    """
    obj = _prepare_trie(trie, get_storage_root)

    root_node = encode_internal_node(patricialize(obj, Uint(0)))
    if len(rlp.encode(root_node)) < 32:
        return keccak256(rlp.encode(root_node))
    else:
        assert isinstance(root_node, Bytes)
        return Root(root_node)


def patricialize(
    obj: Mapping[Bytes, Bytes], level: Uint
) -> Optional[InternalNode]:
    """
    Structural composition function.

    Used to recursively patricialize and merkleize a dictionary. Includes
    memoization of the tree structure and hashes.

    Parameters
    ----------
    obj :
        Underlying trie key-value pairs, with keys in nibble-list format.
    level :
        Current trie level.

    Returns
    -------
    node : `ethereum.base_types.Bytes`
        Root node of `obj`.
    """
    if len(obj) == 0:
        return None

    arbitrary_key = next(iter(obj))

    # if leaf node
    if len(obj) == 1:
        leaf = LeafNode(arbitrary_key[level:], obj[arbitrary_key])
        return leaf

    # prepare for extension node check by finding max j such that all keys in
    # obj have the same key[i:j]
    substring = arbitrary_key[level:]
    prefix_length = len(substring)
    for key in obj:
        prefix_length = min(
            prefix_length, common_prefix_length(substring, key[level:])
        )

        # finished searching, found another key at the current level
        if prefix_length == 0:
            break

    # if extension node
    if prefix_length > 0:
        prefix = arbitrary_key[level : level + prefix_length]
        return ExtensionNode(
            prefix,
            encode_internal_node(patricialize(obj, level + prefix_length)),
        )

    branches: List[MutableMapping[Bytes, Bytes]] = []
    for _ in range(16):
        branches.append({})
    value = b""
    for key in obj:
        if len(key) == level:
            # shouldn't ever have an account or receipt in an internal node
            if isinstance(obj[key], (Account, Receipt, Uint)):
                raise AssertionError
            value = obj[key]
        else:
            branches[key[level]][key] = obj[key]

    return BranchNode(
        [
            encode_internal_node(patricialize(branches[k], level + 1))
            for k in range(16)
        ],
        value,
    )

```
`EvmYul/EllipticCurvesPy/trie_root.py`:

```py
import sys
from trie import Trie, root, trie_set
from base_types import Bytes
from typing import (
    Optional,
)

fileName : Bytes = sys.argv[1]
file = open(fileName, "r")
n = int(sys.argv[2])

trie: Trie[Bytes, Optional[Bytes]] = Trie(
        secured=False, default=None
    )

for i in range(n):
    key = file.readline()
    value = file.readline()
    trie_set(trie, bytes.fromhex(key.strip()), bytes.fromhex(value.strip()))
r = root(trie)

print(bytes.hex(r), end = '')

```
`EvmYul/FFI/ffi.c`:

```c
#include <stdint.h>
#include "lean/lean.h"
#include "sha-256.h"
#include <stdio.h>
#include <stdbool.h> 
#include "sha3.h"

#define SHA256_OUTPUT_SIZE 32
#define KECCAK256_OUTPUT_SIZE 32

// #define BLAKE2B_OUTPUT_SIZE 64
#define BLAKE2B_COMPRESS_SIZE 8
#define BLAKE2B_KEY_LENGTH    8

extern lean_obj_res sha256(b_lean_obj_arg input, size_t len) {
  uint8_t hash[SHA256_OUTPUT_SIZE];
  calc_sha_256(hash, lean_sarray_cptr(input), len);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(SHA256_OUTPUT_SIZE));
  for (int i = 0; i < SHA256_OUTPUT_SIZE; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}

// Implementation based on https://github.com/BLAKE2/BLAKE2/
// with # of rounds parameterised from 12 (BLAKE2) to k < 2^32.

uint64_t rotr64(const uint64_t w, const unsigned int c) {
  return (w >> c) | (w << (64 - c));
}

#define G(a, b, c, d, e, f)         \
  do {                              \
    v[a] = v[a] + v[b] + e;         \
    v[d] = rotr64(v[d] ^ v[a], 32); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 24); \
    v[a] = v[a] + v[b] + f;         \
    v[d] = rotr64(v[d] ^ v[a], 16); \
    v[c] = v[c] + v[d];             \
    v[b] = rotr64(v[b] ^ v[c], 63); \
  } while(0)

const uint64_t blake2b_IV[8] = {
  0x6A09E667F3BCC908ULL, 0xBB67AE8584CAA73BULL,
  0x3C6EF372FE94F82BULL, 0xA54FF53A5F1D36F1ULL,
  0x510E527FADE682D1ULL, 0x9B05688C2B3E6C1FULL,
  0x1F83D9ABFB41BD6BULL, 0x5BE0CD19137E2179ULL
};

// Do not repeat the last two rows, we'll be MOD 10,
// as we are going 12 -> k rounds.
const uint8_t blake2b_sigma[10][16] = {
  {0 , 1 , 2 , 3 , 4 , 5 , 6 , 7 , 8 , 9 , 10, 11, 12, 13, 14, 15},
  {14, 10, 4 , 8 , 9 , 15, 13, 6 , 1 , 12, 0 , 2 , 11, 7 , 5 , 3 },
  {11, 8 , 12, 0 , 5 , 2 , 15, 13, 10, 14, 3 , 6 , 7 , 1 , 9 , 4 },
  {7 , 9 , 3 , 1 , 13, 12, 11, 14, 2 , 6 , 5 , 10, 4 , 0 , 15, 8 },
  {9 , 0 , 5 , 7 , 2 , 4 , 10, 15, 14, 1 , 11, 12, 6 , 8 , 3 , 13},
  {2 , 12, 6 , 10, 0 , 11, 8 , 3 , 4 , 13, 7 , 5 , 15, 14, 1 , 9 },
  {12, 5 , 1 , 15, 14, 13, 4 , 10, 0 , 7 , 6 , 3 , 9 , 2 , 8 , 11},
  {13, 11, 7 , 14, 12, 1 , 3 , 9 , 5 , 0 , 15, 4 , 8 , 6 , 2 , 10},
  {6 , 15, 14, 9 , 11, 3 , 0 , 8 , 12, 2 , 13, 7 , 1 , 4 , 10, 5 },
  {10, 2 , 8 , 4 , 7 , 6 , 1 , 5 , 15, 11, 9 , 14, 3 , 12, 13, 0 }
};

static void blake2b_compress_any(
  uint32_t              rounds,
  uint64_t*             h,
  const uint64_t* const m,
  const uint64_t* const t,
  bool                  f
) {
  uint64_t v[16];
  for (int i = 0; i < 8; ++i) {
    v[i] = h[i];
    v[i + 8] = blake2b_IV[i];
  }
  v[12]        ^= t[0];
  v[13]        ^= t[1];
  if (f) v[14] =  ~v[14];

  for (unsigned int i = 0U; i < rounds; ++i) {
    G(0, 4, 8 , 12, m[blake2b_sigma[i % 10][0 ]], m[blake2b_sigma[i % 10][1 ]]);
    G(1, 5, 9 , 13, m[blake2b_sigma[i % 10][2 ]], m[blake2b_sigma[i % 10][3 ]]);
    G(2, 6, 10, 14, m[blake2b_sigma[i % 10][4 ]], m[blake2b_sigma[i % 10][5 ]]);
    G(3, 7, 11, 15, m[blake2b_sigma[i % 10][6 ]], m[blake2b_sigma[i % 10][7 ]]);
    G(0, 5, 10, 15, m[blake2b_sigma[i % 10][8 ]], m[blake2b_sigma[i % 10][9 ]]);
    G(1, 6, 11, 12, m[blake2b_sigma[i % 10][10]], m[blake2b_sigma[i % 10][11]]);
    G(2, 7, 8 , 13, m[blake2b_sigma[i % 10][12]], m[blake2b_sigma[i % 10][13]]);
    G(3, 4, 9 , 14, m[blake2b_sigma[i % 10][14]], m[blake2b_sigma[i % 10][15]]);
  }

  for (int i = 0; i < 8; ++i)
    h[i] ^= v[i] ^ v[i + 8];
}

extern lean_obj_arg blake2compressb64(b_lean_obj_arg input) {
  uint8_t* in = lean_sarray_cptr(input);
  
  // [0; 3] (4 bytes) - big endian, 4 bytes
  uint32_t rounds = (in[3] << 0 * 8) | (in[2] << 1 * 8) |
                    (in[1] << 2 * 8) | ((uint32_t)in[0] << 3 * 8);
  in += 4;

  // [4; 67] (64 bytes) - small endian, 8 bytes, 8 times
  uint64_t h[8];
  for (int i = 0; i < 8; ++i) {
    h[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }
  
  // [68; 195] (128 bytes) - small endian, 8 bytes, 16 times
  uint64_t m[16];
  for (int i = 0; i < 16; ++i) {
    m[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }

  // [196; 211] (16 bytes) - small endian, 8 bytes, 2 times
  uint64_t t[2];
  for (int i = 0; i < 2; ++i) {
    t[i] = ((uint64_t)in[0] << (0 * 8)) | ((uint64_t)in[1] << (1 * 8)) |
           ((uint64_t)in[2] << (2 * 8)) | ((uint64_t)in[3] << (3 * 8)) |
           ((uint64_t)in[4] << (4 * 8)) | ((uint64_t)in[5] << (5 * 8)) |
           ((uint64_t)in[6] << (6 * 8)) | ((uint64_t)in[7] << (7 * 8));
    in += sizeof(uint64_t);
  }

  // [212; 212] (1 bytes) - 0 is false, 1 is true
  bool f = *in;

  blake2b_compress_any(rounds, h, m, t, f);

  lean_obj_res res = lean_mk_empty_byte_array(lean_box(BLAKE2B_COMPRESS_SIZE * sizeof(uint64_t)));

  for (int i = 0; i < BLAKE2B_COMPRESS_SIZE * sizeof(uint64_t); ++i)
    lean_byte_array_push(res, *(((uint8_t*)h) + i));

  return res;
}

extern lean_obj_arg memset_zero(size_t n) {
  lean_object* res = lean_alloc_sarray(1, n, n);
  uint8_t* it = lean_sarray_cptr(res);
  memset(it, 0, n);
  return res;
}

extern lean_obj_arg keccak256(b_lean_obj_arg input, size_t inBytes) {
  uint8_t hash[KECCAK256_OUTPUT_SIZE];
  sha3_HashBuffer(256, SHA3_FLAGS_KECCAK, lean_sarray_cptr(input), inBytes, hash, KECCAK256_OUTPUT_SIZE);
  lean_obj_res res = lean_mk_empty_byte_array(lean_box(KECCAK256_OUTPUT_SIZE));
  for (int i = 0; i < KECCAK256_OUTPUT_SIZE; ++i)
    lean_byte_array_push(res, hash[i]);
  return res;
}

```
`EvmYul/FFI/ffi.lean`:

```lean
namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
opaque ByteArray.zeroes (n : USize) : ByteArray

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi

```
`EvmYul/MachineState.lean`:

```lean
import Batteries

import EvmYul.Maps.ByteMap
import EvmYul.UInt256
import Batteries.Data.HashMap

namespace EvmYul

open Batteries

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`  `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  gasAvailable        : UInt256
  activeWords         : UInt256
  memory              : ByteArray
  returnData          : ByteArray
  H_return            : ByteArray
  deriving Inhabited

-- inductive WordSize := | Standard | Single

-- def WordSize.toNat (this : WordSize) : ℕ :=
--   match this with
--     | WordSize.Standard => 32
--     | WordSize.Single   => 1

-- instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end EvmYul

```
`EvmYul/MachineStateOps.lean`:

```lean
import Batteries.Data.RBMap

import EvmYul.MachineState

import EvmYul.SpongeHash.Keccak256

namespace EvmYul

def writeBytes
  (source : ByteArray)
  (sourceAddr : ℕ)
  (self : MachineState)
  (destAddr len : ℕ)
 : MachineState :=
  { self with
      memory := source.write sourceAddr self.memory destAddr len
  }

namespace MachineState

open Batteries (RBMap)

-- Appendix H, (320)
def M (s f l : ℕ) : ℕ :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    -- The addition is not subject to s²⁵⁶ division (at least that's what MSTORE suggests)
    max s ((f + l + 31) / 32)

def x : ByteArray := "hello".toUTF8
def y : ByteArray := "kokusho".toUTF8

def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  writeBytes source 0 self addr.toNat numOctets

def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩ then ⟨0⟩ else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

def msize (self : MachineState) : UInt256 :=
  self.activeWords * ⟨32⟩

def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := self.lookupMemory spos
  let self :=
    { self with
      activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
    }
  (val, self)

def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := self.writeWord spos sval
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
  }

def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := writeBytes ⟨#[UInt8.ofNat sval.toNat]⟩ 0 self spos.toNat 1
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 1)
  }

def mcopy (self : MachineState) (writeStart readStart s : UInt256) : MachineState :=
  let self := writeBytes self.memory readStart.toNat self writeStart.toNat s.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat (max writeStart.toNat readStart.toNat) s.toNat)
  }

def gas (self : MachineState) : UInt256 :=
  self.gasAvailable

section ReturnData

def setReturnData (self : MachineState) (r : ByteArray) : MachineState :=
  { self with returnData := r }

def setHReturn (self : MachineState) (r : ByteArray) : MachineState :=
  { self with H_return := r }

def returndatasize (self : MachineState) : UInt256 :=
  .ofNat self.returnData.size

def returndataat (self : MachineState) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.toNat 0

def returndatacopy (self : MachineState) (mstart rstart size : UInt256) : MachineState :=
  let self := writeBytes self.returnData rstart.toNat self mstart.toNat size.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }


def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
  { self with
    H_return := self.memory.readWithPadding mstart.toNat s.toNat
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  let self := self.evmReturn mstart s
  { self with
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

end ReturnData

def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  let kec := ffi.KEC bytes
  let newMachineState :=
    { self with activeWords := .ofNat (M self.activeWords.toNat mstart.toNat s.toNat) }
  (.ofNat (fromByteArrayBigEndian kec), newMachineState)

section Gas

def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := .ofNat gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul

```
`EvmYul/Maps/AccountMap.lean`:

```lean
/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import EvmYul.Wheels

import EvmYul.Maps.StorageMap

import EvmYul.State.Account
import EvmYul.State.AccountOps

namespace EvmYul

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Batteries.RBMap AccountAddress α compare
abbrev AccountMap (τ : OperationType) := AddrMap (Account τ)
abbrev PersistentAccountMap (τ : OperationType) := AddrMap (PersistentAccountState τ)
def AccountMap.toPersistentAccountMap (τ : OperationType) (a : AccountMap τ) : PersistentAccountMap τ :=
  a.mapVal (λ _ acc ↦ acc.toPersistentAccountState)

def AccountMap.increaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : AccountMap τ
:=
  match σ.find? addr with
    | none => σ.insert addr {(default : Account τ) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.decreaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match σ.find? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (σ.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
def AccountMap.transferBalance (τ : OperationType) (σ : AccountMap τ) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match (σ.decreaseBalance τ from_addr amount) with
    | .none => .none
    | .some σ' => σ'.increaseBalance τ to_addr amount

def toExecute (τ : OperationType) (σ : AccountMap τ) (t : AccountAddress) : ToExecute τ :=
  if /- t is a precompiled account -/ t ∈ π then
    ToExecute.Precompiled t
  else Id.run do
    match τ with
      | .EVM =>
        -- We use the code directly without an indirection a'la `codeMap[t]`.
        let .some tDirect := σ.find? t | ToExecute.Code default
        ToExecute.Code tDirect.code
      | .Yul =>
        let .some tDirect := σ.find? t | ToExecute.Code default
        ToExecute.Code tDirect.code

def L_S (σ : PersistentAccountMap .EVM) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState .EVM) : ByteArray × ByteArray :=
    (ffi.KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState .EVM) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

def stateTrieRoot (σ : PersistentAccountMap .EVM) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    let b₁ := EvmYul.toHex entry.1
    let b₂ := EvmYul.toHex entry.2
    (b₁, b₂)

end RemoveLater

end EvmYul

```
`EvmYul/Maps/ByteMap.lean`:

```lean
/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap

import EvmYul.Wheels

namespace EvmYul

section RemoveLater

abbrev ByteMap := Batteries.RBMap UInt256 UInt8 compare

end RemoveLater

end EvmYul

```
`EvmYul/Maps/StorageMap.lean`:

```lean
/-
We need a more unified approach to maps.

This file shouldn't exist; but it does for now.
`Finmap`s have terrible computational behaviour, one needs some ordering lemmas to make them compute.

In `Conform`, we use `Lean.RBMap`, although we would ideally use `Batteries.RBMap`, but the `Lean.Json`
uses `Lean.RBMap`, which means that we would need an additional cast to `Batteries.RBMap`.

Furthermore, replacing everything with either of the `RBMaps` would then reintroduce this mess,
but with ordering lemmas needed for some `Decidable` instances.

When time allows, I suggest we replace everything with `Batteries.RBMap` and prove the reasoning lemmas we need.
This way, we get decent performance AND the ability to conveniently reason about the structure
a'la `Finmap`.

TODO - All of this is very ugly.
-/

import Batteries.Data.RBMap
import Mathlib.Data.Multiset.Sort

import EvmYul.Wheels
import EvmYul.State.TrieRoot
import EvmYul.SpongeHash.Keccak256

import EvmYul.FFI.ffi

namespace EvmYul

section RemoveLater

abbrev Storage : Type := Batteries.RBMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def Storage.toEvmYulStorage (self : Storage) : EvmYul.Storage :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def toBlobs (pair : UInt256 × UInt256) : Option (String × String) := do
  let kec := ffi.KEC pair.1.toByteArray
  let rlp ← RLP (.𝔹 (BE pair.2.toNat))
  pure (EvmYul.toHex kec, EvmYul.toHex rlp)

def computeTrieRoot (storage : Storage) : Option ByteArray :=
  match Array.mapM toBlobs storage.1.toArray with
    | none => .none
    | some pairs => (ByteArray.ofBlob (blobComputeTrieRoot pairs)).toOption

end RemoveLater

end EvmYul

```
`EvmYul/Operations.lean`:

```lean
import EvmYul.UInt256
import EvmYul.MachineState

import Mathlib.Data.Finmap

namespace EvmYul

set_option autoImplicit true

inductive OperationType where
  | Yul
  | EVM
  deriving DecidableEq, Repr

namespace Operation

section Operation

/--
  Stop and Arithmetic Operations
-/
inductive SAOp (τ : OperationType) : Type where
  /--
    Stop: halts program execution
    δ: 0 ; α : 0
  -/
  | protected STOP : SAOp τ
  /--
    ADD: adds two stack values.
    δ: 2 ; α : 1
  -/
  | protected ADD : SAOp τ
  /--
    MUL: multiplies two stack values.
    δ: 2 ; α : 1
  -/
  | protected MUL : SAOp τ
  /--
    SUB: subtracts two stack values.
    δ: 2 ; α : 1
  -/
  | protected SUB : SAOp τ
  /--
    DIV: divides two stack values.
    δ: 2 ; α: 1
  -/
  | protected DIV : SAOp τ
  /--
    SDIV: signed integer division
    δ: 2 ; α: 1
  -/
  | protected SDIV : SAOp τ
  /--
    MOD: Modulo remainder operation
    δ: 2 ; α: 1
  -/
  | protected MOD : SAOp τ
  /--
    SMOD: signed integer remainder
    δ: 2 ; α: 1
  -/
  | protected SMOD : SAOp τ
  /--
    ADDMOD: addition modulo operation
    δ: 3 ; α: 1
  -/
  | protected ADDMOD : SAOp τ
  /--
    MULMOD: multiplication modulo operation
    δ: 3 ; α: 1
  -/
  | protected MULMOD : SAOp τ
  /--
    EXP: Exponential operation
    δ:2 ; α: 1
  -/
  | protected EXP : SAOp τ
  /--
    SIGNEXTEND: Extend length of two's complement signed integer
    δ: 2 ; α: 1
  -/
  | protected SIGNEXTEND : SAOp τ
  deriving DecidableEq, Repr

/--
  Comparison & Bitwise Logic Operations
-/
inductive CBLOp (τ : OperationType) : Type where
  /--
    LT: less than comparison
    δ: 2 ; α: 1
  -/
  | protected LT : CBLOp τ
  /--
    GT: greater than comparison
    δ: 2 ; α: 1
  -/
  | protected GT : CBLOp τ
  /--
    SLT: signed less-than comparison
    δ:2 ; α: 1
  -/
  | protected SLT : CBLOp τ
  /--
    SGT: signed greater-than comparison
    δ: 2 ; α: 1
  -/
  | protected SGT : CBLOp τ
  /--
    EQ: equality test
    δ:2 ; α : 1
  -/
  | protected EQ : CBLOp τ
  /--
    ISZERO: simple not operation
    δ: 1 ; α : 1
  -/
  | protected ISZERO : CBLOp τ
  /--
    AND: bitwise and
    δ:2 ; α: 1
  -/
  | protected AND : CBLOp τ
  /--
    OR: bitwise or
    δ: 2 ; α: 1
  -/
  | protected OR : CBLOp τ
  /--
    XOR: bitwise xor
    δ: 2 ; α: 1
  -/
  | protected XOR : CBLOp τ
  /--
    NOT: bitwise not
    δ:1 ; α: 1
  -/
  | protected NOT : CBLOp τ
  /--
    BYTE: retrieve single byte from a word
    δ:2 ; α:1
  -/
  | protected BYTE : CBLOp τ
  /--
    SHL: shift left operation
    δ:2 ; α: 1
  -/
  | protected SHL : CBLOp τ
  /--
    SHR: logical shift right operation
    δ:2 ; α:1
  -/
  | protected SHR : CBLOp τ
  /--
    SAR: arithmetical shift right operation
    δ:2 ; α:1
  -/
  | protected SAR : CBLOp τ
  deriving DecidableEq, Repr

/--
  Keccak operation.
-/
inductive KOp : OperationType → Type where
  /--
    KECCAK256: compute KECCAK256 hash
    δ:2 ; α: 1
  -/
  | protected KECCAK256 : KOp τ
  deriving DecidableEq, Repr

/--
  Environment Information.
-/
inductive EOp : OperationType → Type where
  /--
    ADDRESS: get the address of current executing account
    δ:0 ; α: 1
  -/
  | protected ADDRESS : EOp τ
  /--
    BALANCE: get the balance of an input account
    δ:1 ; α: 1
  -/
  | protected BALANCE : EOp τ
  /--
    ORIGIN: get execution origination address
    δ:0 ; α: 1
  -/
  | protected ORIGIN : EOp τ
  /--
    CALLER: returns the caller address
    δ: 0 ; α: 1
  -/
  | protected CALLER : EOp τ
  /--
    CALLVALUE: get deposited value by the instruction / transaction
    responsible for this execution.
    δ: 0 ; α: 1
  -/
  | protected CALLVALUE : EOp τ
  /--
    CALLDATALOAD: get input data of current environment
    δ: 1 ;  α: 1
  -/
  | protected CALLDATALOAD : EOp τ
  /--
    CALLDATASIZE: get size of input data in current environment
    δ: 0 ; α: 1
  -/
  | protected CALLDATASIZE : EOp τ
  /--
    CALLDATACOPY: copy input data from environment to memory
    δ: 3 ; α: 0
  -/
  | protected CALLDATACOPY : EOp τ
  /--
    CODESIZE: get the size of code running in current environment
    δ:0 ; α: 1
  -/
  | protected GASPRICE : EOp τ
  /--
    CODECOPY: Copy code running in current environment to memory
    δ: 3 ; α: 0
  -/
  | protected CODESIZE : EOp τ
  /--
    GASPRICE: Gas price in current execution environment
    δ: 0 ; α: 1
  -/
  | protected CODECOPY : EOp τ
  /--
    EXTCODESIZE: get the size of an account's code
    δ:1 ; α: 1
  -/
  | protected EXTCODESIZE : EOp τ
  /--
    EXTCODECOPY: copy an account's code to memory
    δ: 4 ; α: 0
  -/
  | protected EXTCODECOPY : EOp τ
  /--
    RETURNDATASIZE: get the size of output data from the previous call
                    from the current environment.
    δ: 0 ; α: 1
  -/
  | protected RETURNDATASIZE : EOp τ
  /--
    RETURNDATACOPY: copy output data from previous call to memory
    δ: 3 ; α: 0
  -/
  | protected RETURNDATACOPY : EOp τ
  /--
    EXTCODEHASH: get hash of an account's code
    δ: 1 ; α: 1
  -/
  | protected EXTCODEHASH : EOp τ
  deriving DecidableEq, Repr

/--
  Block Information.
-/
inductive BOp : OperationType → Type where
  /--
    BLOCKHASH: get the hash of one of the 256 most recent blocks
    δ:1 ; α: 1
  -/
  | protected BLOCKHASH : BOp τ
  /--
    COINBASE: get current's block beneficiary address
    δ: 0 ; α: 1
  -/
  | protected COINBASE : BOp τ
  /--
    TIMESTAMP: get current block's timestamp
    δ: 0 ; α: 1
  -/
  | protected TIMESTAMP : BOp τ
  /--
    NUMBER: get current block's number
    δ: 0 ; α: 1
  -/
  | protected NUMBER : BOp τ
  | protected PREVRANDAO : BOp τ
  /--
    GASLIMIT: get the gas limit for the current block
    δ: 0 ; α: 1
  -/
  | protected GASLIMIT : BOp τ
  /--
    CHAINID: returns the chainid, β
    δ: 0 ; α: 1
  -/
  | protected CHAINID : BOp τ
  /--
    SELFBALANCE: get the balance of the current executing account
    δ: 0 ; α: 1
  -/
  | protected SELFBALANCE : BOp τ
  | protected BASEFEE : BOp τ
  | protected BLOBHASH : BOp τ
  | protected BLOBBASEFEE : BOp τ
  deriving DecidableEq, Repr

/--
  Stack, Memory, Storage and Flow Operations
-/
inductive SMSFOp : OperationType → Type where
  /--
    POP: remove an item from the stack
    δ: 1 ; α: 0
  -/
  | protected POP : SMSFOp τ
  /--
    MLOAD: load word from memory
    δ: 1 ; α: 1
  -/
  | protected MLOAD : SMSFOp τ
  /--
    MSTORE: save word in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE : SMSFOp τ
  /--
    SLOAD: load word from storage
    δ: 1 ; α: 1
  -/
  | protected SLOAD : SMSFOp τ
  /--
    SSTORE: Save word to storage
    δ:2 ; α: 0
  -/
  | protected SSTORE : SMSFOp τ
  /--
    MSTORE8: save byte in memory
    δ: 2 ; α: 0
  -/
  | protected MSTORE8 : SMSFOp τ
  /--
    JUMP: modify program counter
    δ:1 ; α: 0
  -/
  | protected JUMP : SMSFOp .EVM
  /--
    JUMPI: conditionally modify program counter
    δ: 2 ; α: 0
  -/
  | protected JUMPI : SMSFOp .EVM
  /--
    PC: get program counter before increment
    δ: 0 ; α: 1
  -/
  | protected PC : SMSFOp .EVM
  /--
    MSIZE: get the size of active memory in bytes
    δ: 0 ; α: 1
  -/
  | protected MSIZE : SMSFOp τ
  /--
    GAS: get the amount of available gas
    δ: 0 ; α: 1
  -/
  | protected GAS : SMSFOp τ
  /--
    JUMPDEST: mark a valid destination for jumps
    δ: 0 ; α: 0
  -/
  | protected JUMPDEST : SMSFOp .EVM
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TLOAD: load word from transient memory
    δ: 1 ; α: 1
  -/
  | protected TLOAD : SMSFOp τ
  /--
    EIP-1153
    https://eips.ethereum.org/EIPS/eip-1153
    TSTORE: Save word to transient memory
    δ: 2 ; α: 0
  -/
  | protected TSTORE : SMSFOp τ
  /--
    EIPS-5656
    MCOPY: copy memory areas
    δ: 3 ; α: 0
  -/
  | protected MCOPY : SMSFOp τ  deriving DecidableEq, Repr

/--
  Push operations.

  PUSH0 : pushes `0` to stack.
    δ: 0 ; α: 1

  PUSHn : pushes n bytes to stack.
    δ: 0 ; α: 1
-/
inductive POp : Type where
  | protected PUSH0 : POp
  | protected PUSH1 : POp
  | protected PUSH2 : POp
  | protected PUSH3 : POp
  | protected PUSH4 : POp
  | protected PUSH5 : POp
  | protected PUSH6 : POp
  | protected PUSH7 : POp
  | protected PUSH8 : POp
  | protected PUSH9 : POp
  | protected PUSH10 : POp
  | protected PUSH11 : POp
  | protected PUSH12 : POp
  | protected PUSH13 : POp
  | protected PUSH14 : POp
  | protected PUSH15 : POp
  | protected PUSH16 : POp
  | protected PUSH17 : POp
  | protected PUSH18 : POp
  | protected PUSH19 : POp
  | protected PUSH20 : POp
  | protected PUSH21 : POp
  | protected PUSH22 : POp
  | protected PUSH23 : POp
  | protected PUSH24 : POp
  | protected PUSH25 : POp
  | protected PUSH26 : POp
  | protected PUSH27 : POp
  | protected PUSH28 : POp
  | protected PUSH29 : POp
  | protected PUSH30 : POp
  | protected PUSH31 : POp
  | protected PUSH32 : POp
  deriving DecidableEq, Repr

/--
  Duplicate Operations.

  DUPn: duplicates the nth item on the stack.
    δ: n ; α: n + 1
-/
inductive DOp : Type where
  | protected DUP1
  | protected DUP2
  | protected DUP3
  | protected DUP4
  | protected DUP5
  | protected DUP6
  | protected DUP7
  | protected DUP8
  | protected DUP9
  | protected DUP10
  | protected DUP11
  | protected DUP12
  | protected DUP13
  | protected DUP14
  | protected DUP15
  | protected DUP16
  deriving DecidableEq, Repr

/--
  Exchange Operations.

  SWAPn: swaps the 1st and nth element of the stack.
    δ: n + 1 ; α: n + 1

-/
inductive ExOp : Type where
  | protected SWAP1  : ExOp
  | protected SWAP2  : ExOp
  | protected SWAP3  : ExOp
  | protected SWAP4  : ExOp
  | protected SWAP5  : ExOp
  | protected SWAP6  : ExOp
  | protected SWAP7  : ExOp
  | protected SWAP8  : ExOp
  | protected SWAP9  : ExOp
  | protected SWAP10 : ExOp
  | protected SWAP11 : ExOp
  | protected SWAP12 : ExOp
  | protected SWAP13 : ExOp
  | protected SWAP14 : ExOp
  | protected SWAP15 : ExOp
  | protected SWAP16 : ExOp
  deriving DecidableEq, Repr

/--
  Logging Operations.

  LOGn: append log record with n topics.
    δ: n + 2 ; α : 0
-/
inductive LOp : OperationType → Type where
  | protected LOG0 : LOp τ
  | protected LOG1 : LOp τ
  | protected LOG2 : LOp τ
  | protected LOG3 : LOp τ
  | protected LOG4 : LOp τ
  deriving DecidableEq, Repr

/--
  System Operations.
-/
inductive SOp : OperationType → Type where
  /--
    CREATE: create a new account with associated code
    δ: 3 ; α: 1
  -/
  | protected CREATE : SOp τ
  /--
    CALL: message call into an account
    δ: 7 ; α: 1
  -/
  | protected CALL : SOp τ
  /--
    CALLCODE: message call into this account with an alternative account's code
    δ: 7 ; α: 1
  -/
  | protected CALLCODE : SOp τ
  /--
    RETURN: Halt execution returning output data
    δ: 2 ; α: 0
  -/
  | protected RETURN : SOp τ
  /--
    DELEGATECALL: message call into this account with an alternative account's code
                  but persisting the current values for sender and value
    δ: 6 ; α: 1
  -/
  | protected DELEGATECALL : SOp τ
  /--
    CREATE2: create a new account with associated code
    δ: 4 ; α: 1
  -/
  | protected CREATE2 : SOp τ
  /--
    STATICCALL: static message call into an account
    δ: 6 ; α: 1
  -/
  | protected STATICCALL : SOp τ
  /--
    REVERT: halt execution reverting state changes but returning data and remaining gas
    δ: 2 ; α: 0
  -/
  | protected REVERT : SOp τ
  /--
    INVALID: invalid opcode
    δ: ∅ ; α: ∅
  -/
  | protected INVALID : SOp τ
  /--
    SELFDESTRUCT: halt and send entire balance to target.
    Deprecated; see EIP-6780
    δ: 1 ; α: 0
  -/
  | protected SELFDESTRUCT : SOp τ
  deriving DecidableEq, Repr

end Operation

end Operation

open Operation

inductive Operation : OperationType → Type where
  | protected StopArith    : SAOp   τ → Operation τ
  | protected CompBit      : CBLOp  τ → Operation τ
  | protected Keccak       : KOp    τ → Operation τ
  | protected Env          : EOp    τ → Operation τ
  | protected Block        : BOp    τ → Operation τ
  | protected StackMemFlow : SMSFOp τ → Operation τ
  | protected Push         : POp      → Operation .EVM
  | protected Dup          : DOp      → Operation .EVM
  | protected Exchange     : ExOp     → Operation .EVM
  | protected Log          : LOp    τ → Operation τ
  | protected System       : SOp    τ → Operation τ
  deriving DecidableEq, Repr
namespace Operation

@[match_pattern]
abbrev STOP       {τ : OperationType} : Operation τ := .StopArith .STOP
abbrev ADD        {τ : OperationType} : Operation τ := .StopArith .ADD
abbrev MUL        {τ : OperationType} : Operation τ := .StopArith .MUL
abbrev SUB        {τ : OperationType} : Operation τ := .StopArith .SUB
abbrev DIV        {τ : OperationType} : Operation τ := .StopArith .DIV
abbrev SDIV       {τ : OperationType} : Operation τ := .StopArith .SDIV
abbrev MOD        {τ : OperationType} : Operation τ := .StopArith .MOD
abbrev SMOD       {τ : OperationType} : Operation τ := .StopArith .SMOD
abbrev ADDMOD     {τ : OperationType} : Operation τ := .StopArith .ADDMOD
abbrev MULMOD     {τ : OperationType} : Operation τ := .StopArith .MULMOD
abbrev EXP        {τ : OperationType} : Operation τ := .StopArith .EXP
abbrev SIGNEXTEND {τ : OperationType} : Operation τ := .StopArith .SIGNEXTEND

abbrev LT     {τ : OperationType} : Operation τ := .CompBit .LT
abbrev GT     {τ : OperationType} : Operation τ := .CompBit .GT
abbrev SLT    {τ : OperationType} : Operation τ := .CompBit .SLT
abbrev SGT    {τ : OperationType} : Operation τ := .CompBit .SGT
abbrev EQ     {τ : OperationType} : Operation τ := .CompBit .EQ
abbrev ISZERO {τ : OperationType} : Operation τ := .CompBit .ISZERO
abbrev AND    {τ : OperationType} : Operation τ := .CompBit .AND
abbrev OR     {τ : OperationType} : Operation τ := .CompBit .OR
abbrev XOR    {τ : OperationType} : Operation τ := .CompBit .XOR
abbrev NOT    {τ : OperationType} : Operation τ := .CompBit .NOT
abbrev BYTE   {τ : OperationType} : Operation τ := .CompBit .BYTE
abbrev SHL    {τ : OperationType} : Operation τ := .CompBit .SHL
abbrev SHR    {τ : OperationType} : Operation τ := .CompBit .SHR
abbrev SAR    {τ : OperationType} : Operation τ := .CompBit .SAR

abbrev KECCAK256 {τ : OperationType} : Operation τ := .Keccak .KECCAK256

abbrev ADDRESS        {τ : OperationType} : Operation τ := .Env .ADDRESS
abbrev BALANCE        {τ : OperationType} : Operation τ := .Env .BALANCE
abbrev ORIGIN         {τ : OperationType} : Operation τ := .Env .ORIGIN
abbrev CALLER         {τ : OperationType} : Operation τ := .Env .CALLER
abbrev CALLVALUE      {τ : OperationType} : Operation τ := .Env .CALLVALUE
abbrev CALLDATALOAD   {τ : OperationType} : Operation τ := .Env .CALLDATALOAD
abbrev CALLDATASIZE   {τ : OperationType} : Operation τ := .Env .CALLDATASIZE
abbrev CALLDATACOPY   {τ : OperationType} : Operation τ := .Env .CALLDATACOPY
abbrev CODESIZE       {τ : OperationType} : Operation τ := .Env .CODESIZE
abbrev GASPRICE       {τ : OperationType} : Operation τ := .Env .GASPRICE
abbrev CODECOPY       {τ : OperationType} : Operation τ := .Env .CODECOPY
abbrev EXTCODECOPY    {τ : OperationType} : Operation τ := .Env .EXTCODECOPY
abbrev EXTCODESIZE    {τ : OperationType} : Operation τ := .Env .EXTCODESIZE
abbrev RETURNDATASIZE {τ : OperationType} : Operation τ := .Env .RETURNDATASIZE
abbrev RETURNDATACOPY {τ : OperationType} : Operation τ := .Env .RETURNDATACOPY
abbrev EXTCODEHASH    {τ : OperationType} : Operation τ := .Env .EXTCODEHASH

abbrev BLOCKHASH   {τ : OperationType} : Operation τ := .Block .BLOCKHASH
abbrev COINBASE    {τ : OperationType} : Operation τ := .Block .COINBASE
abbrev TIMESTAMP   {τ : OperationType} : Operation τ := .Block .TIMESTAMP
abbrev NUMBER      {τ : OperationType} : Operation τ := .Block .NUMBER
abbrev PREVRANDAO  {τ : OperationType} : Operation τ := .Block .PREVRANDAO
abbrev GASLIMIT    {τ : OperationType} : Operation τ := .Block .GASLIMIT
abbrev CHAINID     {τ : OperationType} : Operation τ := .Block .CHAINID
abbrev SELFBALANCE {τ : OperationType} : Operation τ := .Block .SELFBALANCE
abbrev BASEFEE     {τ : OperationType} : Operation τ := .Block .BASEFEE
abbrev BLOBHASH    {τ : OperationType} : Operation τ := .Block .BLOBHASH
abbrev BLOBBASEFEE {τ : OperationType} : Operation τ := .Block .BLOBBASEFEE

abbrev POP     {τ : OperationType}   : Operation τ    := .StackMemFlow .POP
abbrev MLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .MLOAD
abbrev MSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE
abbrev SLOAD   {τ : OperationType}   : Operation τ    := .StackMemFlow .SLOAD
abbrev SSTORE  {τ : OperationType}   : Operation τ    := .StackMemFlow .SSTORE
abbrev MSTORE8 {τ : OperationType}   : Operation τ    := .StackMemFlow .MSTORE8
abbrev JUMP                          : Operation .EVM := .StackMemFlow .JUMP
abbrev JUMPI                         : Operation .EVM := .StackMemFlow .JUMPI
abbrev PC                            : Operation .EVM    := .StackMemFlow .PC
abbrev MSIZE   {τ : OperationType}   : Operation τ    := .StackMemFlow .MSIZE
abbrev GAS     {τ : OperationType}   : Operation τ    := .StackMemFlow .GAS
abbrev JUMPDEST                      : Operation .EVM := .StackMemFlow .JUMPDEST
abbrev TLOAD   {τ : OperationType} : Operation τ    := .StackMemFlow .TLOAD
abbrev TSTORE  {τ : OperationType} : Operation τ    := .StackMemFlow .TSTORE
abbrev MCOPY   {τ : OperationType} : Operation τ := .StackMemFlow .MCOPY

abbrev PUSH0  : Operation .EVM := .Push .PUSH0
abbrev PUSH1  : Operation .EVM := .Push .PUSH1
abbrev PUSH2  : Operation .EVM := .Push .PUSH2
abbrev PUSH3  : Operation .EVM := .Push .PUSH3
abbrev PUSH4  : Operation .EVM := .Push .PUSH4
abbrev PUSH5  : Operation .EVM := .Push .PUSH5
abbrev PUSH6  : Operation .EVM := .Push .PUSH6
abbrev PUSH7  : Operation .EVM := .Push .PUSH7
abbrev PUSH8  : Operation .EVM := .Push .PUSH8
abbrev PUSH9  : Operation .EVM := .Push .PUSH9
abbrev PUSH10 : Operation .EVM := .Push .PUSH10
abbrev PUSH11 : Operation .EVM := .Push .PUSH11
abbrev PUSH12 : Operation .EVM := .Push .PUSH12
abbrev PUSH13 : Operation .EVM := .Push .PUSH13
abbrev PUSH14 : Operation .EVM := .Push .PUSH14
abbrev PUSH15 : Operation .EVM := .Push .PUSH15
abbrev PUSH16 : Operation .EVM := .Push .PUSH16
abbrev PUSH17 : Operation .EVM := .Push .PUSH17
abbrev PUSH18 : Operation .EVM := .Push .PUSH18
abbrev PUSH19 : Operation .EVM := .Push .PUSH19
abbrev PUSH20 : Operation .EVM := .Push .PUSH20
abbrev PUSH21 : Operation .EVM := .Push .PUSH21
abbrev PUSH22 : Operation .EVM := .Push .PUSH22
abbrev PUSH23 : Operation .EVM := .Push .PUSH23
abbrev PUSH24 : Operation .EVM := .Push .PUSH24
abbrev PUSH25 : Operation .EVM := .Push .PUSH25
abbrev PUSH26 : Operation .EVM := .Push .PUSH26
abbrev PUSH27 : Operation .EVM := .Push .PUSH27
abbrev PUSH28 : Operation .EVM := .Push .PUSH28
abbrev PUSH29 : Operation .EVM := .Push .PUSH29
abbrev PUSH30 : Operation .EVM := .Push .PUSH30
abbrev PUSH31 : Operation .EVM := .Push .PUSH31
abbrev PUSH32 : Operation .EVM := .Push .PUSH32

abbrev DUP1  : Operation .EVM := .Dup .DUP1
abbrev DUP2  : Operation .EVM := .Dup .DUP2
abbrev DUP3  : Operation .EVM := .Dup .DUP3
abbrev DUP4  : Operation .EVM := .Dup .DUP4
abbrev DUP5  : Operation .EVM := .Dup .DUP5
abbrev DUP6  : Operation .EVM := .Dup .DUP6
abbrev DUP7  : Operation .EVM := .Dup .DUP7
abbrev DUP8  : Operation .EVM := .Dup .DUP8
abbrev DUP9  : Operation .EVM := .Dup .DUP9
abbrev DUP10 : Operation .EVM := .Dup .DUP10
abbrev DUP11 : Operation .EVM := .Dup .DUP11
abbrev DUP12 : Operation .EVM := .Dup .DUP12
abbrev DUP13 : Operation .EVM := .Dup .DUP13
abbrev DUP14 : Operation .EVM := .Dup .DUP14
abbrev DUP15 : Operation .EVM := .Dup .DUP15
abbrev DUP16 : Operation .EVM := .Dup .DUP16

abbrev SWAP1  : Operation .EVM := .Exchange .SWAP1
abbrev SWAP2  : Operation .EVM := .Exchange .SWAP2
abbrev SWAP3  : Operation .EVM := .Exchange .SWAP3
abbrev SWAP4  : Operation .EVM := .Exchange .SWAP4
abbrev SWAP5  : Operation .EVM := .Exchange .SWAP5
abbrev SWAP6  : Operation .EVM := .Exchange .SWAP6
abbrev SWAP7  : Operation .EVM := .Exchange .SWAP7
abbrev SWAP8  : Operation .EVM := .Exchange .SWAP8
abbrev SWAP9  : Operation .EVM := .Exchange .SWAP9
abbrev SWAP10 : Operation .EVM := .Exchange .SWAP10
abbrev SWAP11 : Operation .EVM := .Exchange .SWAP11
abbrev SWAP12 : Operation .EVM := .Exchange .SWAP12
abbrev SWAP13 : Operation .EVM := .Exchange .SWAP13
abbrev SWAP14 : Operation .EVM := .Exchange .SWAP14
abbrev SWAP15 : Operation .EVM := .Exchange .SWAP15
abbrev SWAP16 : Operation .EVM := .Exchange .SWAP16

abbrev LOG0 {τ : OperationType} : Operation τ := .Log .LOG0
abbrev LOG1 {τ : OperationType} : Operation τ := .Log .LOG1
abbrev LOG2 {τ : OperationType} : Operation τ := .Log .LOG2
abbrev LOG3 {τ : OperationType} : Operation τ := .Log .LOG3
abbrev LOG4 {τ : OperationType} : Operation τ := .Log .LOG4

abbrev CREATE       {τ : OperationType} : Operation τ := .System .CREATE
abbrev CALL         {τ : OperationType} : Operation τ := .System .CALL
abbrev CALLCODE     {τ : OperationType} : Operation τ := .System .CALLCODE
abbrev RETURN       {τ : OperationType} : Operation τ := .System .RETURN
abbrev DELEGATECALL {τ : OperationType} : Operation τ := .System .DELEGATECALL
abbrev CREATE2      {τ : OperationType} : Operation τ := .System .CREATE2
abbrev STATICCALL   {τ : OperationType} : Operation τ := .System .STATICCALL
abbrev REVERT       {τ : OperationType} : Operation τ := .System .REVERT
abbrev INVALID      {τ : OperationType} : Operation τ := .System .INVALID
abbrev SELFDESTRUCT {τ : OperationType} : Operation τ := .System .SELFDESTRUCT

def isPush {τ : OperationType} : Operation τ → Bool
  | .Push _ => true
  | _ => false

def isJump {τ : OperationType} : Operation τ → Bool
  | .JUMP => true
  | .JUMPI => true
  | _ => false

def isPC {τ : OperationType} : Operation τ → Bool
  | .PC => true
  | _ => false

def isJumpdest {τ : OperationType} : Operation τ → Bool
  | .JUMPDEST => true
  | _ => false

def isDup {τ : OperationType} : Operation τ → Bool
  | .Dup _ => true
  | _ => false

def isSwap {τ : OperationType} : Operation τ → Bool
  | .Exchange _ => true
  | _ => false

def isCreate {τ : OperationType} : Operation τ → Bool
  | .CREATE => true
  | .CREATE2 => true
  | _ => false

def isCall {τ : OperationType} : Operation τ → Bool
  | .CALL => true
  | .CALLCODE => true
  | .DELEGATECALL => true
  | .STATICCALL => true
  | _ => false


end Operation

open EvmYul.UInt256

def exp (a b : UInt256) : UInt256 :=
  a ^ b

abbrev fromBool := Bool.toUInt256

def lt (a b : UInt256) :=
  fromBool (a < b)

def gt (a b : UInt256) :=
  fromBool (a > b)

-- def slt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.slt a b)

-- def sgt (a b : UInt256) :=
--   fromBool (EvmYul.UInt256.sgt a b)

def eq (a b : UInt256) :=
  fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end EvmYul

open EvmYul

```
`EvmYul/PerformIO.lean`:

```lean
unsafe def unsafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ :=
  match unsafeIO io with
    | Except.ok    a => a
    | Except.error e => panic! s!"unsafePerformIO was a not great idea after all: {e}"

@[implemented_by unsafePerformIO]
def totallySafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ := Inhabited.default

```
`EvmYul/PointEval.lean`:

```lean
import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobPointEval (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/point_evaluation.py", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s

```
`EvmYul/Pretty.lean`:

```lean
/-
Human-eyeball friendly version of various data used throughout the project.
Mostly used for debugging, possibly for reporting.

The function for pretty printing is always `<Datatype>.pretty (self : Datatype) : String`
modulo parametricity.
-/

import EvmYul.Operations

import Conform.Wheels

namespace EvmYul

/--
Strip the existing `repr` a'la:
- EvmYul.Operation.Push (EvmYul.Operation.POp.PUSH1) → PUSH1

This breaks the moment that `Repr` changes its behaviour; it is fine for the time being.
-/
def Operation.pretty {τ} (self : Operation τ) : String :=
  let reprStr := ToString.toString <| repr self
  let lastComponent := reprStr.splitOn "." |>.getLast!
  lastComponent.take lastComponent.length.pred

/--
`Finmap`s are not very computation-friendly and so the API is ever so slightly meh;
do feel encouraged to sorry out the order properties and just point it to an instance of `LE`.

TODO(not critical) - Unify all the maps used throught the formalisation one day.
-/
def Finmap.pretty {α β : Type} [ToString α] [ToString β]
                               [LE ((_ : α) × β)]
                               [IsTrans ((_ : α) × β) fun x x_1 => x ≤ x_1]
                               [IsAntisymm ((_ : α) × β) fun x x_1 => x ≤ x_1]
                               [IsTotal ((_ : α) × β) fun x x_1 => x ≤ x_1]
                               [DecidableRel fun (x : ((_ : α) × β)) x_1 => x ≤ x_1]
                  (self : Finmap (λ _ : α ↦ β)) : String := Id.run do
  let mut result : String := ""
  for ⟨k, v⟩ in computeToList! self.entries do
    result := result.append s!"{k} → {v}\n"
  return result

end EvmYul

```
`EvmYul/RIP160.lean`:

```lean
import EvmYul.PerformIO
import EvmYul.Wheels
import Conform.Wheels

def blobRIP160 (d : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/rip160.py", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobRIP160 (toHex d)

```
`EvmYul/SHA256.lean`:

```lean
import EvmYul.PerformIO
import EvmYul.Wheels
import Conform.Wheels

def blobSHA256 (d : String) : String :=
  dbg_trace s!"EvmYul/EllipticCurvesPy/sha256.py"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/sha256.py", d]
  }

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)

```
`EvmYul/SNARKV.lean`:

```lean
import EvmYul.Wheels
import EvmYul.PerformIO
import Conform.Wheels

def blobSNARKV (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["EvmYul/EllipticCurvesPy/snarkv.py", data]
  }

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s

```
`EvmYul/Semantics.lean`:

```lean
import EvmYul.Operations

import EvmYul.Yul.State
import EvmYul.Yul.Ast
import EvmYul.Yul.Exception
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps

import EvmYul.EVM.State
import EvmYul.EVM.Exception
import EvmYul.EVM.PrimOps
import EvmYul.EVM.StateOps
import EvmYul.Wheels

import EvmYul.UInt256
import EvmYul.StateOps
import EvmYul.SharedStateOps
import EvmYul.MachineStateOps

import EvmYul.SpongeHash.Keccak256

--

import Mathlib.Data.BitVec
import Mathlib.Data.Array.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

--

namespace EvmYul

section Semantics

open Stack

/--
`Transformer` is the primop-evaluating semantic function type for `Yul` and `EVM`.

- `EVM` is `EVM.State → EVM.State` because the arguments are already contained in `EVM.State.stack`.
- `Yul` is `Yul.State × List Literal → Yul.State × Option Literal` because the evaluation of primops in Yul
  does *not* store results within the state.

Both operations happen in their respecitve `.Exception` error monad.
-/
private abbrev Transformer : OperationType → Type
  | .EVM => EVM.Transformer
  | .Yul => Yul.Transformer

private def dispatchInvalid (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => λ _ ↦ .error .InvalidInstruction
    | .Yul => λ _ _ ↦ .error Yul.Exception.InvalidInstruction

private def dispatchUnary (τ : OperationType) : Primop.Unary → Transformer τ :=
  match τ with
    | .EVM => EVM.execUnOp
    | .Yul => Yul.execUnOp

private def dispatchBinary (τ : OperationType) : Primop.Binary → Transformer τ :=
  match τ with
    | .EVM => EVM.execBinOp
    | .Yul => Yul.execBinOp

private def dispatchTernary (τ : OperationType) : Primop.Ternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execTriOp
    | .Yul => Yul.execTriOp

private def dispatchQuartiary (τ : OperationType) : Primop.Quaternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execQuadOp
    | .Yul => Yul.execQuadOp

private def dispatchExecutionEnvOp (τ : OperationType) (op : ExecutionEnv τ → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.executionEnvOp op
    | .Yul => Yul.executionEnvOp op

private def dispatchUnaryExecutionEnvOp (τ : OperationType) (op : ExecutionEnv τ → UInt256 → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryExecutionEnvOp op
    | .Yul => Yul.unaryExecutionEnvOp op

private def dispatchMachineStateOp (τ : OperationType) (op : MachineState → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.machineStateOp op
    | .Yul => Yul.machineStateOp op

private def dispatchUnaryStateOp (τ : OperationType) (op : State τ → UInt256 → State τ × UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryStateOp op
    | .Yul => Yul.unaryStateOp op

private def dispatchTernaryCopyOp
 (τ : OperationType) (op : SharedState τ → UInt256 → UInt256 → UInt256 → SharedState τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryCopyOp op
    | .Yul => Yul.ternaryCopyOp op

private def dispatchQuaternaryCopyOp
 (τ : OperationType) (op : SharedState τ → UInt256 → UInt256 → UInt256 → UInt256 → SharedState τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.quaternaryCopyOp op
    | .Yul => Yul.quaternaryCopyOp op

private def dispatchBinaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp op
    | .Yul => Yul.binaryMachineStateOp op

private def dispatchTernaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryMachineStateOp op
    | .Yul => Yul.ternaryMachineStateOp op

private def dispatchBinaryMachineStateOp'
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp' op
    | .Yul => Yul.binaryMachineStateOp' op

private def dispatchBinaryStateOp
 (τ : OperationType) (op : State τ → UInt256 → UInt256 → State τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryStateOp op
    | .Yul => Yul.binaryStateOp op

private def dispatchStateOp (τ : OperationType) (op : State τ → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.stateOp op
    | .Yul => Yul.stateOp op

private def dispatchLog0 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log0Op
    | .Yul => Yul.log0Op

private def dispatchLog1 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log1Op
    | .Yul => Yul.log1Op

private def dispatchLog2 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log2Op
    | .Yul => Yul.log2Op

private def dispatchLog3 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log3Op
    | .Yul => Yul.log3Op

private def dispatchLog4 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log4Op
    | .Yul => Yul.log4Op

private def L (n : ℕ) := n - n / 64

def dup (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

-- TODO: Yul halting for `SELFDESTRUCT`
def step {τ : OperationType} (op : Operation τ) (arg : Option (UInt256 × Nat) := .none) : Transformer τ := Id.run do
  let _ : Id Unit := -- For debug logging
    match τ with
      | .EVM => dbg_trace op.pretty; pure ()
      | .Yul => dbg_trace op.pretty; pure ()
  match τ, op with
    -- TODO: Revisit STOP, this is likely not the best way to do it.
    | τ, .STOP =>
      match τ with
        | .EVM => λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
        | .Yul => λ yulState _ ↦ .error (Yul.Exception.YulHalt yulState ⟨0⟩)
    | τ, .ADD =>
      dispatchBinary τ UInt256.add
    | τ, .MUL =>
      dispatchBinary τ UInt256.mul
    | τ, .SUB =>
      dispatchBinary τ UInt256.sub
    | τ, .DIV =>
      dispatchBinary τ UInt256.div
    | τ, .SDIV =>
      dispatchBinary τ UInt256.sdiv
    | τ, .MOD =>
      dispatchBinary τ UInt256.mod
    | τ, .SMOD =>
      dispatchBinary τ UInt256.smod
    | τ, .ADDMOD =>
      dispatchTernary τ UInt256.addMod
    | τ, .MULMOD =>
      dispatchTernary τ UInt256.mulMod
    | τ, .EXP =>
      dispatchBinary τ UInt256.exp
    | τ, .SIGNEXTEND =>
      dispatchBinary τ UInt256.signextend
    | τ, .LT =>
      dispatchBinary τ UInt256.lt
    | τ, .GT =>
      dispatchBinary τ UInt256.gt
    | τ, .SLT =>
      dispatchBinary τ UInt256.slt
    | τ, .SGT =>
      dispatchBinary τ UInt256.sgt
    | τ, .EQ =>
      dispatchBinary τ UInt256.eq
    | τ, .ISZERO =>
      dispatchUnary τ UInt256.isZero
    | τ, .AND =>
      dispatchBinary τ UInt256.land
    | τ, .OR =>
      dispatchBinary τ UInt256.lor
    | τ, .XOR =>
      dispatchBinary τ UInt256.xor
    | τ, .NOT =>
      dispatchUnary τ UInt256.lnot
    | τ, .BYTE =>
      dispatchBinary τ UInt256.byteAt
    | τ, .SHL =>
      dispatchBinary τ (flip UInt256.shiftLeft)
    | τ, .SHR =>
      dispatchBinary τ (flip UInt256.shiftRight)
    | τ, .SAR =>
      dispatchBinary τ UInt256.sar

    | τ, .KECCAK256 =>
      dispatchBinaryMachineStateOp' τ MachineState.keccak256

    | τ, .ADDRESS =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | τ, .BALANCE =>
      dispatchUnaryStateOp τ EvmYul.State.balance
    | τ, .ORIGIN =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | τ, .CALLER =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | τ, .CALLVALUE =>
      dispatchExecutionEnvOp τ ExecutionEnv.weiValue
    | τ, .CALLDATALOAD =>
      dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | τ, .CALLDATASIZE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
    | τ, .CALLDATACOPY =>
      dispatchTernaryCopyOp τ .calldatacopy
    | .EVM, .CODESIZE =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | .EVM, .CODECOPY =>
      dispatchTernaryCopyOp .EVM .codeCopy
    | τ, .GASPRICE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ExecutionEnv.gasPrice)
    | .EVM, .EXTCODESIZE =>
      dispatchUnaryStateOp .EVM EvmYul.State.extCodeSize
    | .Yul, .EXTCODESIZE =>
      λ _ _ ↦ .error .YulEXTCODESIZENotImplemented
    | .EVM, .EXTCODECOPY =>
      dispatchQuaternaryCopyOp .EVM EvmYul.SharedState.extCodeCopy'
    | τ, .RETURNDATASIZE =>
      dispatchMachineStateOp τ EvmYul.MachineState.returndatasize
    | .EVM, .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .Yul, .RETURNDATACOPY =>
      λ yulState lits ↦
        match lits with
          | [a, b, c] => do
            let mState' := yulState.toSharedState.toMachineState.returndatacopy a b c
            .ok <| (yulState.setMachineState mState', .none)
          | _ => .error .InvalidArguments
    | .EVM, .EXTCODEHASH => dispatchUnaryStateOp .EVM EvmYul.State.extCodeHash

    | τ, .BLOCKHASH => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | τ, .COINBASE => dispatchStateOp τ (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | τ, .TIMESTAMP =>
      dispatchStateOp τ EvmYul.State.timeStamp
    | τ, .NUMBER => dispatchStateOp τ EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | τ, .PREVRANDAO => dispatchExecutionEnvOp τ EvmYul.prevRandao
    | τ, .GASLIMIT => dispatchStateOp τ EvmYul.State.gasLimit
    | τ, .CHAINID => dispatchStateOp τ EvmYul.State.chainId
    | τ, .SELFBALANCE => dispatchStateOp τ EvmYul.State.selfbalance
    | τ, .BASEFEE => dispatchExecutionEnvOp τ EvmYul.basefee
    | τ, .BLOBHASH => dispatchUnaryExecutionEnvOp τ blobhash
    | τ, .BLOBBASEFEE => dispatchExecutionEnvOp τ EvmYul.ExecutionEnv.getBlobGasprice

    | .EVM, .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .EVM, .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow
    | .Yul, .MLOAD => λ yulState lits ↦
        match lits with
          | [a] =>
            let (v, mState') := yulState.toSharedState.toMachineState.mload a
            let yulState' := yulState.setMachineState mState'
            .ok <| (yulState', some v)
          | _ => .error .InvalidArguments
    | τ, .MSTORE =>
      dispatchBinaryMachineStateOp τ MachineState.mstore
    | τ, .MSTORE8 => dispatchBinaryMachineStateOp τ MachineState.mstore8
    | τ, .SLOAD =>
      dispatchUnaryStateOp τ EvmYul.State.sload
    | τ, .SSTORE =>
      dispatchBinaryStateOp τ EvmYul.State.sstore
    | τ, .TLOAD => dispatchUnaryStateOp τ EvmYul.State.tload
    | τ, .TSTORE => dispatchBinaryStateOp τ EvmYul.State.tstore
    | τ, .MSIZE => dispatchMachineStateOp τ MachineState.msize
    | τ, .GAS =>
      dispatchMachineStateOp τ MachineState.gas
    | τ, .MCOPY => dispatchTernaryMachineStateOp τ MachineState.mcopy

    | τ, .LOG0 => dispatchLog0 τ
    | τ, .LOG1 => dispatchLog1 τ
    | τ, .LOG2 => dispatchLog2 τ
    | τ, .LOG3 => dispatchLog3 τ
    | τ, .LOG4 => dispatchLog4 τ
    | .EVM, .RETURN => dispatchBinaryMachineStateOp .EVM MachineState.evmReturn
    | .Yul, .RETURN => λ yulState lits ↦ 
        match (dispatchBinaryMachineStateOp .Yul MachineState.evmReturn) yulState lits with
          | .error e => .error e
          | .ok (s, v) => .error (Yul.Exception.YulHalt s (v.getD ⟨1⟩))
    | .EVM, .REVERT => dispatchBinaryMachineStateOp .EVM MachineState.evmRevert
    | .Yul, .REVERT => λ yulState lits ↦ 
        match (dispatchBinaryMachineStateOp .Yul MachineState.evmRevert) yulState lits with
          | .error e => .error e
          | .ok (_, _) => .error (Yul.Exception.Revert)
    | .EVM, .SELFDESTRUCT =>
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let Iₐ := evmState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 μ₁
            if evmState.createdAccounts.contains Iₐ then
              -- When `SELFDESTRUCT` is executed in the same transaction as the contract was created
              let A' : Substate :=
                { evmState.substate with
                    selfDestructSet :=
                      evmState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account .EVM) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          evmState.accountMap.insert r {σ_r with balance := ⟨0⟩}
                            |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
            else
              /- When SELFDESTRUCT is executed in a transaction that is not the
                same as the contract calling SELFDESTRUCT was created:
              -/
              let A' : Substate :=
                { evmState.substate with
                    accessedAccounts :=
                      evmState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match evmState.lookupAccount Iₐ with
                  | none => dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; evmState.accountMap
                  | some σ_Iₐ  =>
                    match evmState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          evmState.accountMap
                        else
                          evmState.accountMap.insert r
                            {(default : Account .EVM) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          evmState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- Note that if the target is the same as the contract
                          -- calling SELFDESTRUCT there is no net change in balances.
                          -- Unlike the prior specification, Ether will not be burnt in this case.
                          evmState.accountMap
              let evmState' :=
                {evmState with
                  accountMap := accountMap'
                  substate := A'
                }
              .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow
    | .Yul, .SELFDESTRUCT => λ yulState lits ↦
      match lits with
        | [a] =>
            let Iₐ := yulState.executionEnv.codeOwner
            let r : AccountAddress := AccountAddress.ofUInt256 a
              let A' : Substate :=
                { yulState.toState.substate with
                    selfDestructSet :=
                      yulState.toState.substate.selfDestructSet.insert Iₐ
                    accessedAccounts :=
                      yulState.toState.substate.accessedAccounts.insert r
                }
              let accountMap' :=
                match yulState.toState.lookupAccount Iₐ with
                  | none =>
                    dbg_trace "No 'self' found to be destructed; this should probably not be happening;"; yulState.toState.accountMap
                  | some σ_Iₐ  =>
                    match yulState.toState.lookupAccount r with
                      | none =>
                        if σ_Iₐ.balance == ⟨0⟩ then
                          yulState.toState.accountMap
                        else
                          yulState.toState.accountMap.insert r
                            {(default : Account .Yul) with balance := σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                      | some σ_r =>
                        if r ≠ Iₐ then
                          yulState.toState.accountMap.insert r
                            {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                              |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
                        else
                          -- if the target is the same as the contract calling `SELFDESTRUCT` that Ether will be burnt.
                          yulState.toState.accountMap.insert r {σ_r with balance := ⟨0⟩}
                            |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
              let yulState' :=
                yulState.setState
                  { yulState.toState with accountMap := accountMap', substate := A'}
              .ok <| (yulState', none)
        | _ => .error .InvalidArguments
    | τ, .INVALID => dispatchInvalid τ
    | .EVM, .Push .PUSH0 => λ evmState =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push ⟨0⟩)
    | .EVM, .Push _ => λ evmState => do
        let some (arg, argWidth) := arg | .error .StackUnderflow
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
    | .EVM, .JUMP => λ evmState => do
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .JUMPI => λ evmState => do
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmState.pc + ⟨1⟩
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .PC => λ evmState =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
    | .EVM, .JUMPDEST => λ evmState => do
        .ok <| evmState.incrPC
    | .EVM, .DUP1 => dup 1
    | .EVM, .DUP2 => dup 2
    | .EVM, .DUP3 => dup 3
    | .EVM, .DUP4 => dup 4
    | .EVM, .DUP5 => dup 5
    | .EVM, .DUP6 => dup 6
    | .EVM, .DUP7 => dup 7
    | .EVM, .DUP8 => dup 8
    | .EVM, .DUP9 => dup 9
    | .EVM, .DUP10 => dup 10
    | .EVM, .DUP11 => dup 11
    | .EVM, .DUP12 => dup 12
    | .EVM, .DUP13 => dup 13
    | .EVM, .DUP14 => dup 14
    | .EVM, .DUP15 => dup 15
    | .EVM, .DUP16 => dup 16
    | .EVM, .SWAP1 => swap 1
    | .EVM, .SWAP2 => swap 2
    | .EVM, .SWAP3 => swap 3
    | .EVM, .SWAP4 => swap 4
    | .EVM, .SWAP5 => swap 5
    | .EVM, .SWAP6 => swap 6
    | .EVM, .SWAP7 => swap 7
    | .EVM, .SWAP8 => swap 8
    | .EVM, .SWAP9 => swap 9
    | .EVM, .SWAP10 => swap 10
    | .EVM, .SWAP11 => swap 11
    | .EVM, .SWAP12 => swap 12
    | .EVM, .SWAP13 => swap 13
    | .EVM, .SWAP14 => swap 14
    | .EVM, .SWAP15 => swap 15
    | .EVM, .SWAP16 => swap 16
    | .EVM, _ => λ _ ↦ default
    | .Yul, .POP => λ yulState _ ↦ .ok (yulState, .none) -- POP is a no-op for Yul as it discards the value only as a hint to the compiler.
    | .Yul, _ => λ _ _ ↦ default

end Semantics

end EvmYul

```
`EvmYul/SharedState.lean`:

```lean
import EvmYul.State
import EvmYul.MachineState

namespace EvmYul

structure SharedState (τ : OperationType) extends EvmYul.State τ, EvmYul.MachineState
  deriving Inhabited

end EvmYul

```
`EvmYul/SharedStateOps.lean`:

```lean
import EvmYul.SharedState
import EvmYul.StateOps
import EvmYul.MachineStateOps
import EvmYul.MachineState
import EvmYul.Operations
import Mathlib.Data.List.Intervals

namespace EvmYul

namespace SharedState

section Keccak

end Keccak

section Memory

def writeWord {τ} (self : SharedState τ) (addr v : UInt256) : SharedState τ :=
  { self with toMachineState := self.toMachineState.writeWord addr v }


def calldatacopy {τ} (self : SharedState τ) (mstart datastart size : UInt256) : SharedState τ :=
  { self with
    memory := self.executionEnv.calldata.write datastart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def codeCopy  (self : SharedState .EVM) (mstart cstart size : UInt256) : SharedState .EVM :=
  { self with
    memory := self.executionEnv.code.write cstart.toNat self.memory mstart.toNat size.toNat
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }

def extCodeCopy' (self : SharedState .EVM) (acc mstart cstart size : UInt256) : SharedState .EVM :=
  let mstart := mstart.toNat
  let cstart := cstart.toNat
  let size := size.toNat
  let addr := AccountAddress.ofUInt256 acc
  let b : ByteArray := self.toState.lookupAccount addr |>.option .empty (·.code)
  { self with
    memory := b.write cstart self.memory mstart size
    substate := .addAccessedAccount self.toState.substate addr
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart size)
  }

end Memory

def logOp {τ} (μ₀ μ₁ : UInt256) (t : Array UInt256) (sState : SharedState τ) : SharedState τ :=
  let Iₐ := sState.executionEnv.codeOwner
  let mem := sState.memory.readWithPadding μ₀.toNat μ₁.toNat
  { sState with
    substate.logSeries := sState.substate.logSeries.push ⟨Iₐ, t, mem⟩
    activeWords := .ofNat (MachineState.M sState.activeWords.toNat μ₀.toNat μ₁.toNat)
  }

end SharedState

end EvmYul

```
`EvmYul/SpongeHash/Keccak256.lean`:

```lean
/-
  Switch to our Cryptographic repository once open sourced for equational version.

  Use FFI in the meanwhile.
-/

```
`EvmYul/State.lean`:

```lean
import Batteries.Data.RBMap
import Mathlib.Data.Finset.Basic

import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.Account
import EvmYul.State.Block
import EvmYul.State.Substate
import EvmYul.State.Transaction

import EvmYul.Maps.AccountMap

import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Υᵍ`
-/
structure State (τ : OperationType) where
  accountMap          : AccountMap τ
  σ₀                  : AccountMap .EVM
  totalGasUsedInBlock : ℕ
  transactionReceipts  : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv τ
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Batteries.RBSet AccountAddress compare
deriving Inhabited

def State.blockHashes {τ} (self : State τ) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end EvmYul

```
`EvmYul/State/Account.lean`:

```lean
import EvmYul.Maps.StorageMap
import EvmYul.SpongeHash.Keccak256

import EvmYul.UInt256
import EvmYul.Wheels

import EvmYul.Yul.Ast

namespace EvmYul

/--
  Precompiled contract addresses.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`
-/
def π : Batteries.RBSet AccountAddress compare :=
  Batteries.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare

inductive ToExecute (τ : OperationType) where
  | Code (code : Yul.Ast.contractCode τ)
  | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState (τ : OperationType) where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : (Yul.Ast.contractCode τ)
  deriving BEq, Inhabited, Repr

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account (τ : OperationType) extends PersistentAccountState τ where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState .EVM) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

def Account.codeHash (self : (Account .EVM)) : UInt256 :=
  self.toPersistentAccountState.codeHash

end EvmYul

```
`EvmYul/State/AccountOps.lean`:

```lean
import EvmYul.State.Account

import EvmYul.Maps.StorageMap

import EvmYul.Pretty

namespace EvmYul

namespace Account

def lookupStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.storage.findD k ⟨0⟩

def updateStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with storage := self.storage.erase k }
  else
    { self with storage := self.storage.insert k v }

def lookupTransientStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.tstorage.findD k ⟨0⟩

def updateTransientStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with tstorage := self.tstorage.erase k }
  else
    { self with tstorage := self.tstorage.insert k v }

/--
EMPTY(σ, a). Section 4.1., equation 14.
-/
def emptyAccount {τ} (self : Account τ) : Bool :=
  match τ with
    | .EVM => self.code.isEmpty ∧ self.nonce = ⟨0⟩ ∧ self.balance = ⟨0⟩
    | .Yul => false -- Yul statements always hold code.

def addBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let overflow : Bool := self.balance + balance < self.balance
  if overflow then .none
  else .some { self with balance := self.balance + balance }

def subBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let underflow : Bool := self.balance < balance
  if underflow then .none
  else .some { self with balance := self.balance - balance }

end Account

end EvmYul

```
`EvmYul/State/Block.lean`:

```lean
import Mathlib.Data.Finset.Basic

import EvmYul.State.BlockHeader
import EvmYul.State.Transaction
import EvmYul.State.Withdrawal

namespace EvmYul

instance : Repr (Finset BlockHeader) := ⟨λ _ _ ↦ "Dummy Repr for ommers. TODO - change this :)."⟩

structure Transactions where
  trieRoot : ByteArray
  array : Array Transaction
deriving BEq, Inhabited, Repr

structure Withdrawals where
  trieRoot : ByteArray
  array : Array Withdrawal
deriving BEq, Inhabited, Repr

structure RawBlock where
  rlp          : ByteArray
  exception    : List String
deriving BEq, Inhabited, Repr

abbrev RawBlocks := Array RawBlock

structure DeserializedBlock where
  hash         : UInt256
  blockHeader  : BlockHeader
  transactions : Transactions
  withdrawals  : Withdrawals
  exception    : List String
deriving BEq, Inhabited, Repr

abbrev DeserializedBlocks := Array DeserializedBlock

structure ProcessedBlock where
  hash        : UInt256
  blockHeader : BlockHeader
  σ           : AccountMap .EVM
deriving Inhabited

abbrev ProcessedBlocks := Array ProcessedBlock

def validateUInt256
  (b : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception UInt256
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt256.size then throw e
  pure (.ofNat b)

def validateUInt64
  (b : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception UInt64
:= do
  let b := fromByteArrayBigEndian b
  if b ≥ UInt64.size then throw e
  pure (.ofNat b)

def validateAccountAddress
  (a : ByteArray)
  (e : EVM.Exception)
  : Except EVM.Exception AccountAddress
:= do
  if a.size ≠ 20 then throw e
  pure (.ofNat (fromByteArrayBigEndian a))

def deserializeBlock
  (rlp : ByteArray)
  : Except EVM.Exception (UInt256 × BlockHeader × Transactions × Withdrawals)
:= do
  let (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws) ←
    Option.toExceptWith (.BlockException .RLP_STRUCTURES_ENCODING) do
      let .inr [headerRLP, transactionsRLP, _, withdrawalsRLP] ← oneStepRLP rlp | none
      let hash : UInt256 := .ofNat <| fromByteArrayBigEndian <| ffi.KEC headerRLP
      let header ← deserializeRLP headerRLP
      let (.inr transactions) ← oneStepRLP transactionsRLP | none
      let getTrieSnd (t : ByteArray) : Option ByteArray := do
        match ← oneStepRLP t with
          | .inl typePlusPayload => typePlusPayload
          | .inr _ => t
      let transactionTrieRoot ←
        Transaction.computeTrieRoot (← transactions.toArray.mapM getTrieSnd)
      let ts ← transactions.mapM deserializeRLP
      let (.inr withdrawals) ← oneStepRLP withdrawalsRLP | none
      let withdrawalTrieRoot ← Withdrawal.computeTrieRoot withdrawals.toArray
      let ws ← withdrawals.mapM deserializeRLP
      pure (hash, header, transactionTrieRoot, ts, withdrawalTrieRoot, ws)
  let header ← parseHeader header
  let transactions ← parseTransactions (.𝕃 ts)
  let withdrawals ← parseWithdrawals (.𝕃 ws)
  pure (hash, header, ⟨transactionTrieRoot, Array.mk transactions⟩, ⟨withdrawalTrieRoot, Array.mk withdrawals⟩)
 where
  parseWithdrawal : 𝕋 → Except EVM.Exception Withdrawal
    | .𝕃 [.𝔹 globalIndex, .𝔹 validatorIndex, .𝔹 recipient, .𝔹 amount] => do
      pure <|
        .mk
          (← validateUInt64 globalIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateUInt64 validatorIndex (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
          (← validateAccountAddress recipient (.BlockException .RLP_INVALID_ADDRESS))
          (← validateUInt64 amount (.BlockException .RLP_INVALID_FIELD_OVERFLOW_64))
    | _ =>
      dbg_trace "RLP error: parseWithdrawal"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseWithdrawals : 𝕋 → Except EVM.Exception (List Withdrawal)
    | .𝕃 withdrawals => withdrawals.mapM parseWithdrawal
    | .𝔹 ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseWithdrawals"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseStorageKey : 𝕋 → Except EVM.Exception UInt256
    | .𝔹 key => pure <| .ofNat <| fromByteArrayBigEndian key
    | _ =>
      dbg_trace "RLP error: parseStorageKey"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseAccessListEntry : 𝕋 → Except EVM.Exception (AccountAddress × Array UInt256)
    | .𝕃 [.𝔹 accountAddress, .𝕃 storageKeys] => do
      let storageKeys ← storageKeys.mapM parseStorageKey
      let accountAddress : AccountAddress := .ofNat <| fromByteArrayBigEndian accountAddress
      pure (accountAddress, Array.mk storageKeys)
    | _ =>
      dbg_trace "RLP error: parseAccessListEntry"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

  parseBlobVersionHash : 𝕋 → Except EVM.Exception ByteArray
    | .𝔹 hash => pure hash
    | _ =>
      dbg_trace "RLP error: parseBlobVersionHash"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseTransaction : 𝕋 → Except EVM.Exception Transaction
    | .𝔹 typePlusPayload => -- Transaction type > 0
      match deserializeRLP (typePlusPayload.extract 1 typePlusPayload.size) with
        | some -- Type 3 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 maxFeePerBlobGas
            , .𝕃 blobVersionedHashes
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas := .ofNat <| fromByteArrayBigEndian maxFeePerGas
            let maxFeePerBlobGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerBlobGas
            let blobVersionedHashes ←
              blobVersionedHashes.mapM parseBlobVersionHash
            let dynamicFeeTransaction : DynamicFeeTransaction :=
              .mk base withAccessList maxFeePerGas maxPriorityFeePerGas
            pure <| .blob <|
              BlobTransaction.mk
                dynamicFeeTransaction
                  maxFeePerBlobGas
                  blobVersionedHashes
        | some -- Type 2 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 maxPriorityFeePerGas
            , .𝔹 maxFeePerGas
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let maxPriorityFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxPriorityFeePerGas
            let maxFeePerGas :=
              .ofNat <| fromByteArrayBigEndian maxFeePerGas
            pure <| .dynamic <|
              DynamicFeeTransaction.mk
                base
                withAccessList
                maxFeePerGas maxPriorityFeePerGas
        | some -- Type 1 transactions
          (.𝕃
            [ .𝔹 chainId
            , .𝔹 nonce
            , .𝔹 gasPrice
            , .𝔹 gasLimit
            , .𝔹 recipient
            , .𝔹 value
            , .𝔹 p
            , .𝕃 accessList
            , .𝔹 y
            , .𝔹 r
            , .𝔹 s
            ]
          ) => do
            let recipient : Option AccountAddress:=
              if recipient.isEmpty then none
              else some <| .ofNat <| fromByteArrayBigEndian recipient
            let accessList ← accessList.mapM parseAccessListEntry

            let base : Transaction.Base :=
              .mk
                (.ofNat <| fromByteArrayBigEndian nonce)
                (.ofNat <| fromByteArrayBigEndian gasLimit)
                recipient
                (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
                r
                s
                p
            let withAccessList : Transaction.WithAccessList :=
              .mk
                (.ofNat <| fromByteArrayBigEndian chainId)
                accessList
                (.ofNat <| fromByteArrayBigEndian y)
            let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
            pure <| .access <| AccessListTransaction.mk base withAccessList ⟨gasPrice⟩
        | _ =>
          dbg_trace "RLP error: deserializeRLP could not parse non-legacy transaction"
          throw <| .BlockException .RLP_STRUCTURES_ENCODING
    | .𝕃
      [ .𝔹 nonce
      , .𝔹 gasPrice
      , .𝔹 gasLimit
      , .𝔹 recipient
      , .𝔹 value
      , .𝔹 p
      , .𝔹 w
      , .𝔹 r
      , .𝔹 s
      ] => do
        let recipient : Option AccountAddress:=
          if recipient.isEmpty then none
          else some <| .ofNat <| fromByteArrayBigEndian recipient

        let base : Transaction.Base :=
          Transaction.Base.mk
            (.ofNat <| fromByteArrayBigEndian nonce)
            (.ofNat <| fromByteArrayBigEndian gasLimit)
            recipient
            (← validateUInt256 value (.TransactionException .RLP_INVALID_VALUE))
            r
            s
            p
        let gasPrice := .ofNat <| fromByteArrayBigEndian gasPrice
        let w := .ofNat <| fromByteArrayBigEndian w
        pure <| .legacy <| LegacyTransaction.mk base ⟨gasPrice⟩ w
    | _ =>
      dbg_trace "RLP error: parseTransaction"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseTransactions : 𝕋 → Except EVM.Exception (List Transaction)
    | .𝕃 transactions => transactions.mapM parseTransaction
    | .𝔹 ⟨#[]⟩ => pure []
    | _ =>
      dbg_trace "RLP error: parseTransactions"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING
  parseHeader : 𝕋 → Except EVM.Exception BlockHeader
    | .𝕃
      [ .𝔹 parentHash
      , .𝔹 uncleHash
      , .𝔹 coinbase
      , .𝔹 stateRoot
      , .𝔹 transactionsTrie
      , .𝔹 receiptTrie
      , .𝔹 bloom
      , .𝔹 difficulty
      , .𝔹 number
      , .𝔹 gasLimit
      , .𝔹 gasUsed
      , .𝔹 timestamp
      , .𝔹 extraData
      , .𝔹 mixHash
      , .𝔹 nonce
      , .𝔹 baseFeePerGas
      , .𝔹 withdrawalsRoot
      , .𝔹 blobGasUsed
      , .𝔹 excessBlobGas
      , .𝔹 parentBeaconBlockRoot
      ]
      => pure <|
        BlockHeader.mk
          (.ofNat <| fromByteArrayBigEndian parentHash)
          (.ofNat <| fromByteArrayBigEndian uncleHash)
          (.ofNat <| fromByteArrayBigEndian coinbase)
          (.ofNat <| fromByteArrayBigEndian stateRoot)
          transactionsTrie
          receiptTrie
          bloom
          (fromByteArrayBigEndian difficulty)
          (fromByteArrayBigEndian number)
          (fromByteArrayBigEndian gasLimit)
          (fromByteArrayBigEndian gasUsed)
          (fromByteArrayBigEndian timestamp)
          extraData
          (.ofNat <| fromByteArrayBigEndian nonce)
          (.ofNat <| fromByteArrayBigEndian mixHash)
          (fromByteArrayBigEndian baseFeePerGas)
          parentBeaconBlockRoot
          withdrawalsRoot
          (.ofNat <| fromByteArrayBigEndian blobGasUsed)
          (.ofNat <| fromByteArrayBigEndian excessBlobGas)
    | _ =>
      dbg_trace "Block header has wrong RLP structure"
      throw <| .BlockException .RLP_STRUCTURES_ENCODING

end EvmYul

```
`EvmYul/State/BlockHeader.lean`:

```lean
import EvmYul.UInt256
import EvmYul.Wheels

namespace EvmYul

/--
`BlockHeader`. `H_<x>`. Section 4.3.

`parentHash`    `p`
`ommersHash`    `o`
`beneficiary`   `c`
`stateRoot`     `r`
`transRoot`     `t`
`receiptRoot`   `e`
`logsBloom`     `b`
`difficulty`    `d` [deprecated]
`number`        `i`
`gasLimit`      `l`
`gasUsed`       `g`
`timestamp`     `s`
`extraData`     `x`
`chainId`       `n` 
`nonce`         `n` [deprecated]
`baseFeePerGas` `f`
`withdrawalsRoot` (EIP-4895)
`parentBeaconBlockRoot` (EIP-4877)
-/
structure BlockHeader where
  parentHash    : UInt256
  ommersHash    : UInt256
  beneficiary   : AccountAddress
  stateRoot     : UInt256
  transRoot     : ByteArray
  receiptRoot   : ByteArray
  logsBloom     : ByteArray
  -- Officially deprecated, but checked in `wrongDifficulty_Cancun`
  difficulty    : ℕ
  number        : ℕ
  gasLimit      : ℕ
  gasUsed       : ℕ
  timestamp     : ℕ
  extraData     : ByteArray
  nonce         : UInt64
  prevRandao    : UInt256
  baseFeePerGas : ℕ
  parentBeaconBlockRoot : ByteArray
  withdrawalsRoot : ByteArray
  blobGasUsed     : UInt64
  excessBlobGas   : UInt64
deriving DecidableEq, Inhabited, Repr, BEq

def prettyDifference (h₁ h₂ : BlockHeader) : String := Id.run do
  let mut result := ""
  if h₁.parentHash != h₂.parentHash then result := result ++ "different parentHash\n"
  if h₁.ommersHash != h₂.ommersHash then result := result ++ "different ommersHash\n"
  if h₁.beneficiary != h₂.beneficiary then result := result ++ "different beneficiary\n"
  if h₁.stateRoot != h₂.stateRoot then result := result ++ "different stateRoot\n"
  if h₁.transRoot != h₂.transRoot then result := result ++ "different transRoot\n"
  if h₁.receiptRoot != h₂.receiptRoot then result := result ++ "different receiptRoot\n"
  if h₁.logsBloom != h₂.logsBloom then result := result ++ "different logsBloom\n"
  if h₁.difficulty != h₂.difficulty then result := result ++ "different difficulty\n"
  if h₁.number != h₂.number then result := result ++ "different number\n"
  if h₁.gasLimit != h₂.gasLimit then result := result ++ "different gasLimit\n"
  if h₁.gasUsed != h₂.gasUsed then result := result ++ "different gasUsed\n"
  if h₁.timestamp != h₂.timestamp then result := result ++ "different timestamp\n"
  if h₁.extraData != h₂.extraData then result := result ++ "different extraData\n"
  if h₁.nonce != h₂.nonce then result := result ++ "different nonce\n"
  if h₁.prevRandao != h₂.prevRandao then result := result ++ "different prevRandao\n"
  if h₁.baseFeePerGas != h₂.baseFeePerGas then result := result ++ "different baseFeePerGas\n"
  if h₁.parentBeaconBlockRoot != h₂.parentBeaconBlockRoot then result := result ++ "different parentBeaconBlockRoot\n"
  if h₁.withdrawalsRoot != h₂.withdrawalsRoot then result := result ++ "different withdrawalsRoot\n"
  if h₁.blobGasUsed != h₂.blobGasUsed then result := result ++ "different blobGasUsed\n"
  if h₁.excessBlobGas != h₂.excessBlobGas then result := result ++ "different excessBlobGas\n"

  result

def TARGET_BLOB_GAS_PER_BLOCK := 393216

def calcExcessBlobGas (parent : BlockHeader) : Option UInt64 := do
  if parent.excessBlobGas.toNat + parent.blobGasUsed.toNat < TARGET_BLOB_GAS_PER_BLOCK then
    pure ⟨0⟩
  else
    pure <| .ofNat <| parent.excessBlobGas.toNat + parent.blobGasUsed.toNat - TARGET_BLOB_GAS_PER_BLOCK

-- See https://eips.ethereum.org/EIPS/eip-4844#gas-accounting
partial def fakeExponential0 (i output factor numerator denominator : ℕ) : (numeratorAccum : ℕ) → ℕ
  | 0 =>
    output / denominator
  | numeratorAccum =>
    let output := output + numeratorAccum
    let numeratorAccum := (numeratorAccum * numerator) / (denominator * i)
    let i := i + 1
    fakeExponential0 i output factor numerator denominator numeratorAccum

def fakeExponential (factor numerator denominator : ℕ) : ℕ :=
  fakeExponential0 1 0 factor numerator denominator (factor * denominator)

def MIN_BASE_FEE_PER_BLOB_GAS := 1
def BLOB_BASE_FEE_UPDATE_FRACTION := 3338477

def BlockHeader.getBlobGasprice (h : BlockHeader) : ℕ :=
  fakeExponential
    MIN_BASE_FEE_PER_BLOB_GAS
    h.excessBlobGas.toNat
    BLOB_BASE_FEE_UPDATE_FRACTION

end EvmYul

```
`EvmYul/State/ExecutionEnv.lean`:

```lean
import EvmYul.Wheels
import EvmYul.UInt256
import EvmYul.State.BlockHeader
import EvmYul.Yul.Ast

namespace EvmYul

/--
The execution envorinment `I` `ExecutionEnv`. Section 9.3.
- `codeOwner` `Iₐ`
- `sender`    `Iₒ`
- `source`    `Iₛ`
- `weiValue`  `Iᵥ`
- `calldata` `I_d`
- `code`      `I_b`
- `gasPrice`  `Iₚ`
- `header`    `I_H`
- `depth`     `Iₑ`
- `perm`      `I_w`
-/
structure ExecutionEnv (τ : OperationType) where
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  calldata : ByteArray
  code      : (Yul.Ast.contractCode τ)
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  blobVersionedHashes : List ByteArray
  deriving BEq, Inhabited, Repr

def prevRandao {τ} (e : ExecutionEnv τ) : UInt256 :=
  e.header.prevRandao

def basefee {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.baseFeePerGas

def ExecutionEnv.getBlobGasprice {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.getBlobGasprice

def blobhash {τ} (e : ExecutionEnv τ) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option ⟨0⟩
    (.ofNat ∘ fromByteArrayBigEndian)

end EvmYul

```
`EvmYul/State/Substate.lean`:

```lean
import Batteries.Data.RBMap
import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.Account

namespace EvmYul

/--
Not important for reasoning about Substate, this is currently done to get some nice performance properties
of the `Batteries.RBMap`.

TODO - to reason about the model, we will be better off with `Finset` or some such -
without the requirement of ordering.

The current goal is to make sure that the model is executable and conformance-testable
before we make it easy to reason about.
-/
def Substate.storageKeysCmp (sk₁ sk₂ : AccountAddress × UInt256) : Ordering :=
  lexOrd.compare sk₁ sk₂

structure LogEntry where
  address : AccountAddress
  topics  : Array UInt256
  data    : ByteArray
deriving BEq, Inhabited, Repr

def LogEntry.to𝕋 : LogEntry → 𝕋
  | ⟨address, topics, data⟩ =>
    .𝕃
      [ .𝔹 address.toByteArray
      , .𝕃 <| topics.toList.map (.𝔹 ∘ UInt256.toByteArray)
      , .𝔹 data
      ]

abbrev LogSeries := Array LogEntry

def LogSeries.to𝕋 (logSeries : LogSeries) : 𝕋 :=
  .𝕃 (logSeries.toList.map LogEntry.to𝕋)

/--
The `Substate` `A`. Section 6.1.
- `selfDestructSet`    `Aₛ`
- `touchedAccounts`    `Aₜ`
- `refundBalance`      `Aᵣ`
- `accessedAccounts`   `Aₐ`
- `accessedStorageKey` `Aₖ`
- `logSeries`          `Aₗ`
-/
structure Substate where
  selfDestructSet     : Batteries.RBSet AccountAddress compare
  touchedAccounts     : Batteries.RBSet AccountAddress compare
  refundBalance       : UInt256
  accessedAccounts    : Batteries.RBSet AccountAddress compare
  accessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp
  logSeries           : LogSeries
  deriving BEq, Inhabited, Repr

/--
  (63) `A0 ≡ (∅, (), ∅, 0, π, ∅)`
-/
def A0 : Substate := { (default : Substate) with accessedAccounts := π }

-- See the Bloom filter function M
def bloomFilter (a : Array ByteArray) : ByteArray  :=
  let zeroes : ByteArray := ffi.ByteArray.zeroes 256
  a.foldl set3Bits zeroes
 where
  setBit (bytes256 : ByteArray) (bitIndex : ℕ) : ByteArray :=
    let byteIndex := 255 - bitIndex / 8
    let mask : UInt8 := .ofNat <| 1 <<< (bitIndex % 8)
    let newByte := bytes256[byteIndex]! ||| mask
    bytes256.set! byteIndex newByte
  bitIndices (x : ByteArray) : List ℕ :=
    let kec := ffi.KEC x
    let lowOrder11Bits := λ b ↦ b &&& (1<<<11 - 1)
    [ kec.readWithPadding 0 2
    , kec.readWithPadding 2 2
    , kec.readWithPadding 4 2
    ].map (lowOrder11Bits ∘ fromByteArrayBigEndian)
  set3Bits acc b := bitIndices b |>.foldl setBit acc

def Substate.joinLogs (substate : Substate) : Array ByteArray :=
  Array.flatten <|
    substate.logSeries.map
      λ ⟨a, as, _⟩ ↦ (as.map UInt256.toByteArray).push a.toByteArray

end EvmYul

```
`EvmYul/State/SubstateOps.lean`:

```lean
import EvmYul.State.Substate

namespace EvmYul

namespace Substate

def addAccessedAccount (self : Substate) (addr : AccountAddress) : Substate :=
  { self with accessedAccounts := self.accessedAccounts.insert addr }

def addAccessedStorageKey (self : Substate) (sk : AccountAddress × UInt256) : Substate :=
  { self with accessedStorageKeys := self.accessedStorageKeys.insert sk }

end Substate

end EvmYul

```
`EvmYul/State/Transaction.lean`:

```lean
import Mathlib.Data.List.AList

import EvmYul.UInt256
import EvmYul.Wheels
import EvmYul.State.TrieRoot
import Conform.Wheels
import EvmYul.State.Substate

namespace EvmYul

open Batteries (RBMap RBSet)

-- "All transaction types specify a number of common fields:"
/--
`BaseTransaction`. Section 4.3.

- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
-/
structure Transaction.Base where
  nonce           : UInt256
  gasLimit        : UInt256
  recipient       : Option AccountAddress
  value           : UInt256
  r               : ByteArray
  s               : ByteArray
  data            : ByteArray
deriving BEq, Repr

-- "EIP-2930 (type 1) and EIP-1559 (type 2) transactions also have:""
/--
`AccessList`. EIP-2930.
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
-/
structure Transaction.WithAccessList where
  chainId : UInt256
  accessList : List (AccountAddress × Array UInt256)
  yParity : UInt256
deriving BEq, Repr

-- "type 0 and type 1 transactions specify gas price as a single value:"
/--
`WithGasPrice`. Section 4.3.
- `gasPrice` `p`
-/
structure Transaction.WithGasPrice where
  gasPrice : UInt256
deriving BEq, Repr

-- Legacy transactions do not have an `accessList`, while `chainId` and `yParity` for legacy transactions are combined into a single value:
/--
Type 0: `LegacyTransaction`. Section 4.3.
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `gasPrice` `p`
- `w` `w`
-/
structure LegacyTransaction extends Transaction.Base, Transaction.WithGasPrice where
  w: UInt256
deriving BEq, Repr

/-- Type 1: `AccessListTransaction`
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
- `gasPrice` `p`
-/
structure AccessListTransaction
  extends Transaction.Base, Transaction.WithAccessList, Transaction.WithGasPrice
deriving BEq, Repr

/--
Type 2: `DynamicFeeTransaction`
- `nonce`                `n`
- `gasLimit`             `g`
- `recipinet`            `t`
- `value`                `v`
- `r`                    `r`
- `s`                    `s`
- `data`                 `d/i`
- `chainId`              `c`
- `accessList`           `A`
- `yParity`              `y`
- `maxFeePerGas`         `m`
- `maxPriorityFeePerGas` `f`
-/
structure DynamicFeeTransaction extends Transaction.Base, Transaction.WithAccessList where
  maxFeePerGas         : UInt256
  maxPriorityFeePerGas : UInt256
deriving BEq, Repr

structure BlobTransaction extends DynamicFeeTransaction where
  maxFeePerBlobGas  : UInt256
  blobVersionedHashes : List ByteArray
deriving BEq, Repr

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  | blob    : BlobTransaction → Transaction
deriving BEq, Repr

def Transaction.base : Transaction → Transaction.Base
  | legacy t => t.toBase
  | access t => t.toBase
  | dynamic t => t.toBase
  | blob t => t.toBase

def Transaction.getAccessList : Transaction → List (AccountAddress × Array UInt256)
  | legacy _ => []
  | access t => t.accessList
  | dynamic t => t.accessList
  | blob t => t.accessList

def Transaction.type : Transaction → UInt8
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2
  | .blob _ => 3

def Transaction.toBlobs (t : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE t.1))
  let rlp := t.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

def Transaction.computeTrieRoot (ts : Array ByteArray) : Option ByteArray := do
  match Array.mapM Transaction.toBlobs ((Array.range ts.size).zip ts) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

structure TransactionReceipt where
  type                     : UInt8     /- R_x -/
  statusCode               : Bool      /- R_z -/
  cumulativeGasUsedInBlock : ℕ         /- R_u -/
  bloomFilter              : ByteArray /- R_b -/
  logSeries                : LogSeries /- R_l -/
deriving BEq, Inhabited, Repr

def L_R : TransactionReceipt → 𝕋
  | ⟨_, statusCode, cumulativeGasUsedInBlock, bloomFilter, logSeries⟩ =>
  .𝕃
    [ if statusCode then .𝔹 (BE 1) else .𝔹 (BE 0)
    , .𝔹 (BE cumulativeGasUsedInBlock)
    , .𝔹 bloomFilter
    , logSeries.to𝕋
    ]

def TransactionReceipt.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  let rlp ← w.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
def TransactionReceipt.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM TransactionReceipt.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def TransactionReceipt.toTrieValue (r : TransactionReceipt) : ByteArray :=
  let rlp := Option.get! ∘ RLP ∘ L_R <| r
  if r.type = 0 then rlp else ⟨#[r.type]⟩ ++ rlp

end EvmYul

```
`EvmYul/State/TransactionOps.lean`:

```lean
import EvmYul.State.Transaction
import EvmYul.State.BlockHeader
import EvmYul.State.ExecutionEnv

namespace EvmYul

def Transaction.to? : Transaction → Option AccountAddress
  | .legacy t | .access t | .dynamic t | .blob t => t.recipient

def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t | .blob t => t.data

def GAS_PER_BLOB := 2^17
def VERSIONED_HASH_VERSION_KZG : UInt8 := 1

def getTotalBlobGas (t : Transaction) : ℕ :=
  match t with
  | .blob t => GAS_PER_BLOB * t.blobVersionedHashes.length
  | _ => 0

def Transaction.blobVersionedHashes (t : Transaction) : List ByteArray :=
  match t with
  | .blob t => t.blobVersionedHashes
  | _ => []

def calcBlobFee (header: BlockHeader) (t : Transaction) : ℕ :=
  let totalBlobGas := getTotalBlobGas t
  totalBlobGas * header.getBlobGasprice

end EvmYul

```
`EvmYul/State/TrieRoot.lean`:

```lean
import EvmYul.PerformIO
import EvmYul.Wheels

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  -- dbg_trace s!"called blobComputeTrieRoot with an array of size {ws.size}"
  -- dbg_trace s!"called blobComputeTrieRoot with data {ws[0]!.2.length}"
  
  totallySafePerformIO do
    /-
      Yes, this makes testing in parallel technically nondeterministic, but it is also the
      fastest to implement.

      This 'using a file trick' to get around big command line arguments should probably go
      at some point.
    -/
    let entropy ← IO.getRandomBytes 3
    let entropy' ← IO.monoNanosNow
    let inputFile := s!"EvmYul/EllipticCurvesPy/trieInput_{entropy}{entropy'}.txt"
    IO.FS.withFile inputFile .write λ h ↦
      forM ws.toList λ s ↦ do
        h.putStrLn s.1
        h.putStrLn s.2
    let result ← IO.Process.run (pythonCommandOfInput inputFile ws)
    IO.FS.removeFile inputFile
    pure result
 where
  pythonCommandOfInput (inputFile : String) (ws : Array (String × String)) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args :=
      #["EvmYul/EllipticCurvesPy/trie_root.py"]
        ++ #[inputFile]
        ++ #[ws.size.repr]
        -- ++ (ws.map (λ (i, w) ↦ #[i, w])).join
  }

```
`EvmYul/State/Withdrawal.lean`:

```lean
-- Requires the following python packages: pycryptodome

import EvmYul.Wheels
import EvmYul.PerformIO
import EvmYul.Maps.AccountMap
import Conform.Wheels
import EvmYul.EVM.Exception

import EvmYul.State.TrieRoot

open EvmYul ByteArray

/--
EIP-4895: Beacon chain push withdrawals as operations.
- `index` - starting from `0`
- `validator_index`
- `address` - a recipient for the withdrawn ether
- `amount` - a nonzero amount of ether given in Gwei
-/
structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : AccountAddress
  amount : UInt64
deriving Repr, BEq

namespace Withdrawal

def to𝕋 : Withdrawal → 𝕋
  | {index, validatorIndex, address, amount} =>
    .𝕃
      [ .𝔹 (BE index.toFin.val)
      , .𝔹 (BE validatorIndex.toFin.val)
      , .𝔹 (address.toByteArray)
      , .𝔹 (BE amount.toFin.val)
      ]

end Withdrawal

def Withdrawal.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  let rlp ← w.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
def Withdrawal.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM Withdrawal.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def applyWithdrawals
  (σ : AccountMap .EVM)
  (ws : Array Withdrawal)
    :
  AccountMap .EVM
:=
  ws.foldl applyWithdrawal σ
 where
  applyWithdrawal (σ : AccountMap .EVM) (w : Withdrawal) : AccountMap .EVM :=
    if w.amount <= 0 then σ else
      match σ.find? w.address with
        | none =>
          σ.insert w.address {(default : Account .EVM) with balance := .ofNat <| w.amount.toFin.val * 10^9}
        | some ac =>
          σ.insert w.address {ac with balance := .ofNat <| ac.balance.toNat + w.amount.toFin.val * 10^9}

```
`EvmYul/StateOps.lean`:

```lean
import EvmYul.State.SubstateOps
import EvmYul.State.AccountOps

import EvmYul.Maps.AccountMap

import EvmYul.State
import EvmYul.Wheels
import EvmYul.EVM.GasConstants

namespace EvmYul

namespace State

def addAccessedAccount {τ} (self : State τ) (addr : AccountAddress) : State τ :=
  { self with substate := self.substate.addAccessedAccount addr }

def addAccessedStorageKey {τ} (self : State τ) (sk : AccountAddress × UInt256) : State τ :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.
-/
def dead {τ} (σ : AccountMap τ) (addr : AccountAddress) : Bool :=
  σ.find? addr |>.option True Account.emptyAccount

def accountExists {τ} (self : State τ) (addr : AccountAddress) : Bool := self.accountMap.find? addr |>.isSome

def lookupAccount {τ} (self : State τ) (addr : AccountAddress) : Option (Account τ) :=
  self.accountMap.find? addr

def updateAccount {τ} (addr : AccountAddress) (act : Account τ) (self : State τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr act }

def setAccount {τ} (self : State τ) (addr : AccountAddress) (acc : Account τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr acc }

def setSelfAccount {τ} (self : State τ) (acc : Account τ := default) : State τ :=
  self.setAccount self.executionEnv.codeOwner acc

def updateAccount! {τ} (self : State τ) (addr : AccountAddress) (f : Account τ → Account τ) : State τ :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def updateSelfAccount! {τ} (self : State τ) : (Account τ → Account τ) → State τ :=
  self.updateAccount! self.executionEnv.codeOwner

def balance {τ} (self : State τ) (k : UInt256) : State τ × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accountMap.find? addr |>.elim ⟨0⟩ (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State .EVM) : State .EVM :=
  if self.accountExists addr then self else self.updateAccount addr default

def calldataload {τ} (self : State τ) (v : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.calldata.readBytes v.toNat 32

def setNonce! {τ} (self : State τ) (addr : AccountAddress) (nonce : UInt256) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

def setSelfNonce! {τ} (self : State τ) (nonce : UInt256) : State τ :=
  self.setNonce! self.executionEnv.codeOwner nonce

def selfStorage! {τ} (self : State τ) : Storage :=
  self.lookupAccount self.executionEnv.codeOwner |>.getD default |>.storage

section CodeCopy

def extCodeSize (self : State .EVM) (a : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

def extCodeHash (self : State .EVM) (v : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accountMap addr then (newState, ⟨0⟩) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option ⟨0⟩ Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

def blockHash {τ} (self : State τ) (blockNumber : UInt256) : UInt256 :=
  let v := self.executionEnv.header.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then ⟨0⟩
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat ⟨0⟩

def coinBase {τ} (self : State τ) : AccountAddress :=
  self.executionEnv.header.beneficiary

def timeStamp {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.timestamp

def number {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.number

def difficulty {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.difficulty

def gasLimit {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.gasLimit

def chainId {τ} (_ : State τ) : UInt256 := .ofNat EvmYul.chainId

def selfbalance {τ} (self : State τ) : UInt256 :=
  Batteries.RBMap.find? self.accountMap self.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)

def setCode (self : State .EVM) (code : ByteArray) : State .EVM :=
  { self with executionEnv.code := code }

end Blocks

section Storage

def setStorage! {τ} (self : State τ) (addr : AccountAddress) (strg : Storage) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def setSelfStorage! {τ} (self : State τ) : Storage → State τ :=
  self.setStorage! self.executionEnv.codeOwner

def sload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

def sstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  let { storage := σ_Iₐ, .. } := self.accountMap.find! Iₐ
  let v₀ :=
    match self.σ₀.find? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.findD spos ⟨0⟩
  let v := σ_Iₐ.findD spos ⟨0⟩
  let v' := sval

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let newAᵣ : UInt256 :=
    match ΔAᵣ with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - ⟨1⟩
  self.lookupAccount Iₐ |>.option self λ acc ↦
    let self' :=
      self.setAccount Iₐ (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (Iₐ, spos)
    { self' with substate.refundBalance := newAᵣ }

def tload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupTransientStorage (k := spos))
  (self, v)

def tstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)

end Storage

end State

end EvmYul

```
`EvmYul/UInt256.lean`:

```lean
import Init.Data.Nat.Div
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Ring

namespace EvmYul

/-- The size of type `UInt256`, that is, `2^256`. -/
def UInt256.size : ℕ :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size where
  out := (by unfold UInt256.size; simp)

structure UInt256 where
  val : Fin UInt256.size
  deriving BEq, Ord

instance : ToString UInt256 where
  toString a := toString a.val

namespace UInt256

def ofNat (n : ℕ) : UInt256 := Id.run do
  ⟨Fin.ofNat _ n⟩

def toNat (u : UInt256) : ℕ := u.val.val

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

instance {n : ℕ} : OfNat (Fin UInt256.size) n := ⟨Fin.ofNat _ n⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩

end UInt256

end EvmYul

section CastUtils

open EvmYul UInt256

abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
abbrev UInt8.toUInt256 (a : UInt8) : UInt256 :=
  ⟨a.toNat, Nat.lt_trans a.toFin.2 (by decide)⟩
def Bool.toUInt256 (b : Bool) : UInt256 :=
  if b then UInt256.ofNat 1 else UInt256.ofNat 0

@[simp]
lemma Bool.toUInt256_true : true.toUInt256 = UInt256.ofNat 1 := rfl

@[simp]
lemma Bool.toUInt256_false : false.toUInt256 = UInt256.ofNat 0 := rfl

end CastUtils

namespace EvmYul

namespace UInt256

def add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
def sub (a b : UInt256) : UInt256 := ⟨a.val - b.val⟩
def mul (a b : UInt256) : UInt256 := ⟨a.val * b.val⟩
def div (a b : UInt256) : UInt256 := ⟨a.val / b.val⟩
def mod (a b : UInt256) : UInt256 := if b.val == 0 then ⟨0⟩ else ⟨a.val % b.val⟩
def modn (a : UInt256) (n : ℕ) : UInt256 := ⟨Fin.modn a.val n⟩
def land (a b : UInt256) : UInt256  := ⟨Fin.land a.val b.val⟩
def lor (a b : UInt256) : UInt256   := ⟨Fin.lor a.val b.val⟩
def xor (a b : UInt256) : UInt256   := ⟨Fin.xor a.val b.val⟩
def shiftLeft (a b : UInt256) : UInt256  :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val <<< b.val⟩
def shiftRight (a b : UInt256) : UInt256 :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val >>> b.val⟩
-- def lt (a b : UInt256) : Prop := a.1 < b.1
-- def le (a b : UInt256) : Prop := a.1 ≤ b.1
def log2 (a : UInt256) : UInt256 := ⟨Fin.log2 a.val⟩

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩

instance : LT UInt256 where
  lt a b := LT.lt a.val b.val

instance : LE UInt256 where
  le a b := LE.le a.val b.val

instance : Preorder UInt256 where
  le_refl := by intro; apply Nat.le_refl
  le_trans := by intro _ _ _ h₁ h₂ ; apply Nat.le_trans h₁ h₂
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_ge := by intros; rfl

def complement (a : UInt256) : UInt256 := ⟨0 - (a.val + 1)⟩

def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1) - a

def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then ⟨a.val * (-1)⟩
  else a

def fromSigned (a : UInt256) : ℤ :=
  if a.toNat < 2^255 then a.val else - (Nat.xor (UInt256.size - 1) a.val) - 1

def toSigned (i : ℤ) : UInt256 :=
  match i with
    | .ofNat n => ofNat n
    | .negSucc n => ofNat (UInt256.size - 1 - n)

instance : Complement UInt256 := ⟨EvmYul.UInt256.complement⟩

private def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux ⟨1⟩ b n.1

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : Xor UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

instance : DecidableEq UInt256 := λ a b ↦
  match decEq a.val b.val with
    | isTrue h => isTrue (congrArg UInt256.mk h)
    | isFalse h => by
      have neq : ¬ a = b := by
        intro eq
        have eq' : a.val = b.val := congrArg UInt256.val eq
        contradiction
      exact isFalse neq

def decLt (a b : UInt256) : Decidable (a < b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n < m))

def decLe (a b : UInt256) : Decidable (a ≤ b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt256) : Decidable (a < b) := decLt _ _
instance (a b : UInt256) : Decidable (a ≤ b) := UInt256.decLe a b
instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

def eq0 (a : UInt256) : Bool := a == ⟨0⟩

def byteAt (a b : UInt256) : UInt256 :=
  if a > ⟨31⟩ then ⟨0⟩ else
    b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& ⟨0xFF⟩

def sgn (a : UInt256) : ℤ :=
  if 2 ^ 255 <= a.toNat then
    -1
  else
    if eq0 a then 0 else 1

def bigUInt : UInt256 := ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else ⟨(abs a / b).val * -1⟩
  else
    if 2 ^ 255 <= b.toNat then
      ⟨(a / abs b).val * -1⟩
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then ⟨0⟩
  else
    toSigned <| sgn a * (abs a % abs b).toNat

def sltBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b.toNat ≥ 2 ^ 255 then false
    else a < b

def sgtBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b.toNat ≥ 2 ^ 255 then true
    else a > b

abbrev fromBool := Bool.toUInt256

def slt (a b : UInt256) :=
  fromBool (sltBool a b)

def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

def sar (a b : UInt256) : UInt256 :=
  if sltBool b ⟨0⟩
  then UInt256.complement (UInt256.complement b >>> a)
  else b >>> a

private partial def dbg_toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (dbg_toHex (n / 16)) ++ hexDigitRepr (n % 16)

def signextend (a b : UInt256) : UInt256 :=
  if a.toNat ≤ 31 then
    let test_bit := a * ⟨8⟩ + ⟨7⟩
  let sign_bit := ⟨1⟩ <<< test_bit
    if b &&& sign_bit ≠ ⟨0⟩ then
      b ||| (UInt256.size.toUInt256 - sign_bit)
    else b &&& (sign_bit - ⟨1⟩)
  else b

def addMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val + b.val) c.toNat

def mulMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val * b.val) c.toNat

def exp (a b : UInt256) : UInt256 := pow a b

def lt (a b : UInt256) := fromBool (a < b)

def gt (a b : UInt256) := fromBool (a > b)

def eq (a b : UInt256) := fromBool (a = b)

def isZero (a : UInt256) :=
  fromBool (eq0 a)

end UInt256

-- | Convert from a list of little-endian bytes to a natural number.
def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.toFin.val + 2^8 * fromBytes' bs

def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse
def fromByteArrayBigEndian (b : ByteArray) : ℕ := fromBytesBigEndian b.toList

variable {bs : List UInt8}
         {n : ℕ}

-- | A bound for the natural number value of a list of bytes.
private lemma fromBytes'_le : fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold fromBytes'; simp
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

-- | The natural number value of a length 32 list of bytes is < 2^256.
private lemma fromBytes'_UInt256_le (h : bs.length = 32) : fromBytes' bs < 2^256 := by
    have h' := @fromBytes'_le bs
    rw [h] at h'
    exact h'

-- | Convert a natural number into a list of bytes.
private def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := ⟨Nat.mod n UInt8.size, Nat.mod_lt _ (by linarith)⟩
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
private lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [toBytes']
    | .succ n =>
      unfold toBytes'
      simp
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
private lemma toBytes'_UInt256_le (h : n < UInt256.size) : (toBytes' n).length ≤ 32 := toBytes'_le h

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
private def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

-- | The length of a `zeroPadBytes` call is its first argument.
lemma zeroPadBytes_len (h : bs.length ≤ n) : (zeroPadBytes n bs).length = n := by
  unfold zeroPadBytes
  aesop

-- | Appending a bunch of zeroes to a little-endian list of bytes doesn't change its value.
@[simp]
private lemma extend_bytes_zero : fromBytes' (bs ++ List.replicate n 0) = fromBytes' bs := by
  induction bs with
  | nil =>
    simp [fromBytes']
    induction n with
    | zero => simp [List.replicate, fromBytes']
    | succ _ ih => simp [List.replicate, fromBytes']; norm_cast
  | cons _ _ ih => simp [fromBytes', ih]

-- | The ℕ value of a little-endian list of bytes is invariant under right zero-padding up to length 32.
@[simp]
private lemma fromBytes'_zeroPadBytes_32_eq : fromBytes' (zeroPadBytes 32 bs) = fromBytes' bs := extend_bytes_zero

-- | Casting a natural number to a list of bytes and back is the identity.
@[simp]
private lemma fromBytes'_toBytes' {x : ℕ} : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp
    have := Nat.div_lt_self (Nat.zero_lt_succ n) (by decide : 1 < UInt8.size)
    rw [fromBytes'_toBytes']
    simp [UInt8.size, add_comm]
    apply Nat.div_add_mod

def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

private lemma fromBytes_was_good_all_year_long
  (h : bs.length ≤ 32) : fromBytes' bs < 2^256 := by
  have h' := @fromBytes'_le bs
  rw [pow_mul] at h'
  refine lt_of_lt_of_le (b := (2 ^ 8) ^ List.length bs) h' ?lenBs
  case lenBs => rw [←pow_mul]; exact pow_le_pow_right₀ (by decide) (by linarith)

@[simp]
lemma fromBytes_wasnt_naughty : fromBytes! bs < 2^256 := fromBytes_was_good_all_year_long (by simp)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  ⟨fromBytes! bs, fromBytes_wasnt_naughty⟩

def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.1)

def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  .ofNat <| fromBytes' arr.data.toList.reverse

end EvmYul

section HicSuntDracones

def ByteArray.copySlice' (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  if false -- srcOff < 2^64 && destOff < 2^64 && len < 2^64
  then src.copySlice srcOff dest destOff len exact -- NB only when `srcOff`, `destOff` and `len` are sufficiently small
  else let srcData := src.data
       let destData := dest.data
       let sourceChunk := srcData.extract srcOff (srcOff + len)
       let destBegin := destData.extract 0 destOff
       let destEnd := destData.extract (destOff + len) destData.size
       ⟨destBegin ++ sourceChunk ++ destEnd⟩

end HicSuntDracones

```
`EvmYul/Wheels.lean`:

```lean
import EvmYul.UInt256
import Mathlib.Data.Finmap
import EvmYul.FFI.ffi

-- (195)
def BE : ℕ → ByteArray := List.toByteArray ∘ EvmYul.toBytesBigEndian

namespace EvmYul

def chainId : ℕ := 1

def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val.toNat
  ffi.ByteArray.zeroes ⟨32 - b.size⟩ ++ b

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero AccountAddress.size where
  out := (by unfold AccountAddress.size; simp)

abbrev AccountAddress : Type := Fin AccountAddress.size

instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

instance : Inhabited AccountAddress := ⟨Fin.ofNat _ 0⟩

namespace AccountAddress

def ofNat (n : ℕ) : AccountAddress := Fin.ofNat _ n
def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.val % AccountAddress.size)
instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩

def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ffi.ByteArray.zeroes ⟨20 - b.size⟩ ++ b

end AccountAddress

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

instance : Repr ByteArray where
  reprPrec s _ := toHex s

def Identifier := String
instance : ToString Identifier := inferInstanceAs (ToString String)
instance : Inhabited Identifier := inferInstanceAs (Inhabited String)
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)
instance : Repr Identifier := inferInstanceAs (Repr String)

namespace NaryNotation

scoped syntax "!nary[" ident "^" num "]" : term

open Lean in
scoped macro_rules
  | `(!nary[ $idn:ident ^ $nat:num ]) =>
    let rec go (n : ℕ) : MacroM Term :=
      match n with
        | 0     => `($idn)
        | n + 1 => do `($idn → $(←go n))
    go nat.getNat

end NaryNotation

namespace Primop

section

open NaryNotation

def Nullary    := !nary[UInt256 ^ 0]
def Unary      := !nary[UInt256 ^ 1]
def Binary     := !nary[UInt256 ^ 2]
def Ternary    := !nary[UInt256 ^ 3]
def Quaternary := !nary[UInt256 ^ 4]

end

end Primop

end EvmYul

/--
TODO(rework later to a sane version)
-/
instance : DecidableEq ByteArray := by
  rintro ⟨a⟩ ⟨b⟩
  rw [ByteArray.mk.injEq]
  apply decEq

def Option.option {α β : Type} (dflt : β) (f : α -> β) : Option α → β
  | .none => dflt
  | .some x => f x

def Option.toExceptWith {α β : Type} (dflt : β) (x : Option α) : Except β α :=
  x.option (.error dflt) Except.ok

def ByteArray.get? (self : ByteArray) (n : Nat) : Option UInt8 :=
  if h : n < self.size
  then self.get n h
  else .none

partial def Nat.toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (toHex (n / 16)) ++ hexDigitRepr (n % 16)

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

def toHex (bytes : ByteArray) : String :=
  bytes.foldl (init := "") λ acc byte ↦ acc ++ hexOfByte byte

/-- Add `0`s to make the hex representation valid for `ByteArray.ofBlob` -/
def padLeft (n : ℕ) (s : String) :=
  let l := s.length
  if l < n then String.replicate (n - l) '0' ++ s else s

/--
TODO - Well this is ever so slightly unfortunate.
It appears to be the case that some (all?) definitions that have C++ implementations
use 64bit-width integers to hold numeric arguments.

When this assumption is broken, e.g. `n : Nat := 2^64`, the Lean (4.9.0) gives
inernal out of memory error.

This implementation works around the issue at the price of using a slower implementation
in case either of the arguments is too big.
-/
def ByteArray.extract' (a : ByteArray) (b e : Nat) : ByteArray :=
  -- TODO: Shouldn't (`e` - `b`) be < `2^64` instead of `e` since eventually `a.copySlice b empty 0 (e - b)` is called?
  if b < 2^64 && e < 2^64
  then a.extract b e -- NB only when `b` and `e` are sufficiently small
  else ⟨⟨a.toList.drop b |>.take (e - b)⟩⟩

def HexPrefix := "0x"

def TargetSchedule := "Cancun"

def isHexDigitChar (c : Char) : Bool :=
  '0' <= c && c <= '9' || 'a' <= c.toLower && c.toLower <= 'f'

def cToHex? (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9'
  then .ok <| c.toString.toNat!
  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f'
        then let Δ := c.toLower.toNat - 'a'.toNat
            .ok <| 10 + Δ
        else .error s!"Not a hex digit: {c}"

def ofHex? : List Char → Except String UInt8
  | [] => pure 0
  | [msb, lsb] => do pure ∘ UInt8.ofNat <| (← cToHex? msb) * 16 + (← cToHex? lsb)
  | _ => throw "Need two hex digits for every byte."

def Blob := String

instance : Inhabited Blob := inferInstanceAs (Inhabited String)

def Blob.toString : Blob → String := λ blob ↦ blob

instance : ToString Blob := ⟨Blob.toString⟩

def getBlob? (s : String) : Except String Blob :=
  if isHex s then
    let rest := s.drop HexPrefix.length
    if rest.any (not ∘ isHexDigitChar)
    then .error "Blobs must consist of valid hex digits."
    else .ok rest.toLower
  else .error "Input does not begin with 0x."
  where
    isHex (s : String) := s.startsWith HexPrefix

def getBlob! (s : String) : Blob := getBlob? s |>.toOption.get!

def ByteArray.ofBlob (self : Blob) : Except String ByteArray := do
  let chunks ← self.toList.toChunks 2 |>.mapM ofHex?
  pure ⟨chunks.toArray⟩

def ByteArray.readBytes (source : ByteArray) (start size : ℕ) : ByteArray :=
  let read :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  read ++ ffi.ByteArray.zeroes ⟨size - read.size⟩

def ByteArray.readWithoutPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if addr ≥ source.size then .empty else
    let len := min len source.size
    source.extract addr (addr + len)

private def inf := 2^66

def ByteArray.readWithPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if len ≥ 2^64 then
    panic! s!"ByteArray.readWithPadding: can not handle byte arrays of length {len}"
  else
    let read := source.readWithoutPadding addr len
    read ++ ffi.ByteArray.zeroes ⟨len - read.size⟩

inductive 𝕋 where
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋
  deriving Repr, BEq


def lengthRLP (rlp : ByteArray) : Option ℕ :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      some 1
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        some (1 + strLen)
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          some (1 + lenOfStrLen + strLen)
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            some (1 + listLen)
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              some (1 + lenOfListLen + listLen)
            else
              none

partial def separateListRLP (rlp : ByteArray) : Option (List ByteArray) := do
  if rlp.isEmpty then pure []
  else
    let headLen ← lengthRLP rlp
    let head := rlp.readWithoutPadding 0 headLen
    let tail ← separateListRLP (rlp.readWithoutPadding headLen rlp.size)
    pure <| head :: tail

def oneStepRLP (rlp : ByteArray) : Option (Sum ByteArray (List ByteArray)) :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      let data := .inl ⟨#[rlp₀]⟩
      some data
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        let data := .inl (rlp.readWithoutPadding 1 strLen)
        some data
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          let data := .inl (rlp.readWithoutPadding (1 + lenOfStrLen) strLen)
          some data
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            let list ← separateListRLP (rlp.readWithoutPadding 1 listLen)
            some <| .inr list
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              let list ← separateListRLP (rlp.readWithoutPadding (1 + lenOfListLen) listLen)
              some <| .inr list
            else
              none

partial def deserializeRLP (rlp : ByteArray) : Option 𝕋 := do
  match ← oneStepRLP rlp with
    | .inl byteArray =>
      some (.𝔹 byteArray)
    | .inr list =>
      let l ← list.mapM deserializeRLP
      some (.𝕃 l)

private def R_b (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x.get! 0 < 128 then some x
  else
    if x.size < 56 then some <| [⟨128 + x.size⟩].toByteArray ++ x
    else
      if x.size < 2^64 then
        let be := BE x.size
        some <| [⟨183 + be.size⟩].toByteArray ++ be ++ x
      else none

mutual

private def s (l : List 𝕋) : Option ByteArray :=
  match l with
    | [] => some .empty
    | t :: ts =>
      match RLP t, s ts with
        | none     , _         => none
        | _        , none      => none
        | some rlpₗ, some rlpᵣ => rlpₗ ++ rlpᵣ

def R_l (l : List 𝕋) : Option ByteArray :=
  match s l with
    | none => none
    | some s_x =>
      if s_x.size < 56 then
        some <| [⟨192 + s_x.size⟩].toByteArray ++ s_x
      else
        if s_x.size < 2^64 then
          let be := BE s_x.size
          some <| [⟨247 + be.size⟩].toByteArray ++ be ++ s_x
        else none

def RLP (t : 𝕋) : Option ByteArray :=
  match t with
    | .𝔹 ba => R_b ba
    | .𝕃 l => R_l l

end

def myByteArray : ByteArray := ⟨#[1, 2, 3]⟩

def ByteArray.write
  (source : ByteArray)
  (sourceAddr : ℕ)
  (dest : ByteArray)
  (destAddr len : ℕ)
  : ByteArray
:=
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (ffi.ByteArray.zeroes ⟨len⟩).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      let endPaddingAddr := min dest.size (destAddr + len)
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      let sourcePadding := ffi.ByteArray.zeroes ⟨sourcePaddingLength⟩
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding := ffi.ByteArray.zeroes ⟨destPaddingLength⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)

```
`EvmYul/Yul/Ast.lean`:

```lean
/- Yul specification:
https://docs.soliditylang.org/en/v0.8.9/yul.html
-/

import EvmYul.UInt256
import EvmYul.Operations
import EvmYul.Wheels

namespace EvmYul

namespace Yul

namespace Ast

open EvmYul UInt256

abbrev Literal := UInt256
-- def Identifier := String

instance : ToString Identifier := inferInstanceAs (ToString String)

instance : Inhabited Identifier := ⟨""⟩
instance : DecidableEq Identifier := String.decEq

abbrev PrimOp := Operation .Yul

def stringOfPrimOp : PrimOp → String := toString ∘ repr

instance : ToString PrimOp := ⟨stringOfPrimOp⟩

-- https://docs.soliditylang.org/en/latest/yul.html#informal-description-of-yul

abbrev YulFunctionName := String

mutual
  inductive FunctionDefinition where
    | Def : List Identifier → List Identifier → List Stmt → FunctionDefinition
  deriving BEq, Inhabited

  inductive Expr where
    | Call : (PrimOp ⊕ YulFunctionName) → List Expr → Expr
    | Var : Identifier → Expr
    | Lit : Literal → Expr

  -- | The loop constructor 'Stmt.For' has no initialiser because of
  -- https://docs.soliditylang.org/en/latest/internals/optimizer.html#forloopinitrewriter
  inductive Stmt where
    | Block : List Stmt → Stmt
    | Let : List Identifier → Option Expr → Stmt
    | ExprStmtCall : Expr → Stmt
    | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
    | For : Expr → List Stmt → List Stmt → Stmt
    | If : Expr → List Stmt → Stmt
    | Continue : Stmt
    | Break : Stmt
    | Leave : Stmt
    deriving BEq, Inhabited, Repr
end

structure YulContract where
  dispatcher : Yul.Ast.Stmt
  functions : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition)
  deriving Inhabited

instance : Repr YulContract where
  reprPrec _ _ := "YulContract" -- TODO: implement an actual `reprPrec` for YulContract

instance : BEq YulContract where
  beq a b := 
    a.dispatcher == b.dispatcher
    && (a.functions.keys == b.functions.keys &&
        a.functions.all (λ k _ => a.functions.lookup k == b.functions.lookup k))

abbrev contractCode (τ : OperationType) :=
  match τ with
    | OperationType.EVM => ByteArray
    | OperationType.Yul => YulContract

instance {τ} : BEq (contractCode τ) where
  beq a b := match τ with
              | .EVM => a == b
              | .Yul => a == b

instance {τ} : Inhabited (contractCode τ) where
  default := match τ with
                | .EVM => default
                | .Yul => default
              
instance {τ} : Repr (contractCode τ) where
  reprPrec a _ := match τ with
                     | .EVM => reprPrec a 0
                     | .Yul => reprPrec a 0


namespace FunctionDefinition

def params : FunctionDefinition → List Identifier
  | Def params _ _ => params

def rets : FunctionDefinition → List Identifier
  | Def _ rets _ => rets

def body : FunctionDefinition → List Stmt
  | Def _ _ body => body

end FunctionDefinition

end Ast

end Yul

end EvmYul

```
`EvmYul/Yul/Exception.lean`:

```lean
import EvmYul.Yul.State

namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments                              : Exception
  | NotEncodableRLP                               : Exception
  | InvalidInstruction                            : Exception
  | OutOfFuel                                     : Exception
  | StaticModeViolation                           : Exception
  | MissingContract (s : String)                  : Exception
  | MissingContractFunction (s : String)          : Exception
  | InvalidExpression                             : Exception
  | YulEXTCODESIZENotImplemented                  : Exception
  | Revert                                        : Exception
  | YulHalt (state : Yul.State) (value : UInt256) : Exception
  -- | StopInvoked        : Exception

instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .InvalidArguments => "InvalidArguments"
      | .NotEncodableRLP => "NotEncodableRLP"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfFuel => "OutOfFuel"
      | .StaticModeViolation => "StaticModeViolation"
      | .MissingContract s => "MissingContract: " ++ s
      | .MissingContractFunction f => "MissingContractFunction: " ++ f
      | .InvalidExpression => "InvalidExpression"
      | .YulEXTCODESIZENotImplemented => "YulEXTCODESIZENotImplemented"
      | .Revert => "Revert"
      | .YulHalt _ _ => "YulHalt: (holds a state and a value)"


end Yul

end EvmYul

```
`EvmYul/Yul/Interpreter.lean`:

```lean
import Mathlib.Data.Finmap

import EvmYul.Yul.Ast
import EvmYul.Yul.State
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps
import EvmYul.Yul.SizeLemmas
import EvmYul.Yul.Exception

import EvmYul.Semantics

set_option maxHeartbeats 400000 -- Needs more than 200000

namespace EvmYul

namespace Yul

open Ast SizeLemmas

-- ============================================================================
--  INTERPRETER
-- ============================================================================

def head' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
  | .ok (s, rets) => .ok (s, List.head! rets)
  | .error e => .error e

def cons' (arg : Literal) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, arg :: args)
  | .error e => .error e

def reverse' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, args.reverse)
  | .error e => .error e

def multifill' (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
  | .ok (s, rets) => .ok (s.multifill vars rets)
  | .error e => .error e

def setStatic (s : State) (p : Bool) : State :=
  match s with
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint j => .Checkpoint j
  | .Ok sharedState varstore =>
    let executionEnvStatic := { sharedState.executionEnv with
                                perm := p
                              }
    let sharedState' := { sharedState with
                          executionEnv := executionEnvStatic
                        }
    .Ok sharedState' varstore

def buildContractCallEmptyReturnState (s₀ : State) (accountMap₁ : Option (AccountMap .Yul)) (v : Literal) : Except Yul.Exception (State × List Literal) :=
    match s₀ with
    | .OutOfFuel => .error .OutOfFuel
    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
    | .Ok sharedState₀ varstore =>
      let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty,
                                             returnData := ByteArray.empty,
                                             accountMap := accountMap₁.getD s₀.toSharedState.accountMap }
      .ok (.Ok sharedState₁ varstore, [v])

mutual

def primCall (fuel : ℕ) (s₀ : State) (prim : Operation .Yul) (args : List Literal) : Except Yul.Exception (State × List Literal) :=
  do
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel₁ => 
      if ¬s₀.executionEnv.perm ∧ prim ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] then throw .StaticModeViolation
      match prim with
      | .CALL =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner address value)
            match accountMap₁Opt with
              | .none =>
                buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Insufficient funds: return 0 to indicate error, with empty return data 
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024
                then
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.find? address with
                        | .none => 
                          buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                        | .some yulContract =>
                          let executionEnv₁ := { sharedState.executionEnv with
                                                    calldata := calldata₁,
                                                    code := yulContract.code,
                                                    codeOwner := address,
                                                    source := s₀.executionEnv.codeOwner,
                                                    weiValue := value
                                                    depth := s₀.executionEnv.depth + 1
                                                }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁
                                              }
                          let s₁ : State := .Ok sharedState₁ default
                          
                          match callDispatcher fuel₁ .none s₁ with
                          | .error (.YulHalt s₂ _) => 
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                              
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        executionEnv := executionEnv₃,
                                                        H_return := ByteArray.empty
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
                          | .error e => .error e
                          | .ok (s₂, _) =>
                            
                            /- We note here that if:
                                  `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                                then we are writing beyond the theoretical memory size limit.
                                The yellow paper is unclear on the semantics of this (at the time of writing).
                                We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                                And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                                In practice, this is essentially impossible to occur due to the
                                  prohibitively large gas cost of allocating this much memory.
                                  
                                Similarly in other places in `primCall` where `memory₃` is constructed in this way.
                            -/
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                                                
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .STATICCALL =>
        match args with
          | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm then throw .StaticModeViolation
            let s₀Static : State := setStatic s₀ false
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀Static.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
          
              if s₀Static.toSharedState.executionEnv.depth ≥ 1024
              then
                buildContractCallEmptyReturnState s₀Static .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
              else
                match s₀Static with
                | .OutOfFuel => .error .OutOfFuel
                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                | .Ok sharedState varstore =>
                    match s₀Static.sharedState.accountMap.find? address with
                      | .none => 
                          buildContractCallEmptyReturnState s₀Static .none ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                      | .some yulContract =>
                        let executionEnv₁ := { s₀Static.executionEnv with
                                                  calldata := calldata₁,
                                                  code := yulContract.code,
                                                  codeOwner := address,
                                                  source := s₀Static.executionEnv.codeOwner,
                                                  weiValue := ⟨0⟩
                                                  depth := s₀Static.toSharedState.executionEnv.depth + 1
                                              }
                        let sharedState₁ := { sharedState with
                                                executionEnv := executionEnv₁,
                                                memory := ByteArray.mk #[],
                                            }
                        let s₁ : State := .Ok sharedState₁ default
                        
                        match callDispatcher fuel₁ .none s₁ with
                          | .error (.YulHalt s₂ _) =>
                          let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀Static.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                          match s₂ with
                            | .OutOfFuel => .error .OutOfFuel
                            | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                            | .Ok sharedState₂ _ =>
                              -- Restore ExecutionEnv
                              let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                              let sharedState₃ := { sharedState₂ with
                                                      memory := memory₃,
                                                      returnData := s₂.toMachineState.H_return,
                                                      H_return := ByteArray.empty,
                                                      executionEnv := executionEnv₃
                                                  }
                              .ok (setStatic (.Ok sharedState₃ varstore) s₀.executionEnv.perm, [⟨1⟩])
                          | .error e => .error e
                          | .ok (s₂, _) =>
                        
                          let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀Static.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                          match s₂ with
                            | .OutOfFuel => .error .OutOfFuel
                            | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                            | .Ok sharedState₂ _ =>
                              -- Restore ExecutionEnv
                              let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                              let sharedState₃ := { sharedState₂ with
                                                      memory := memory₃,
                                                      returnData := s₂.toMachineState.H_return,
                                                      H_return := ByteArray.empty,
                                                      executionEnv := executionEnv₃
                                                  }
                              .ok (setStatic (.Ok sharedState₃ varstore) s₀.executionEnv.perm, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .CALLCODE =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner s₀.executionEnv.codeOwner value)
            match accountMap₁Opt with
              | .none =>
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Insufficient funds: return 0 to indicate error, with empty return data 
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024
                then
                  buildContractCallEmptyReturnState s₀ accountMap₁ ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.find? address with
                        | .none => 
                            buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                        | .some yulContract =>
                          let executionEnv₁ := { sharedState.executionEnv with
                                                    calldata := calldata₁,
                                                    code := yulContract.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.codeOwner,
                                                    weiValue := value
                                                    depth := s₀.executionEnv.depth + 1
                                                }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁
                                              }
                          let s₁ : State := .Ok sharedState₁ default
                          
                          match callDispatcher fuel₁ yulContract.code s₁ with
                          | .error (.YulHalt s₂ _) =>
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])

                          | .error e => .error e
                          | .ok (s₂, _) =>                            
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .DELEGATECALL =>
        match args with
          | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            if s₀.executionEnv.depth ≥ 1024
            then
              buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
            else
              match s₀ with
              | .OutOfFuel => .error .OutOfFuel
              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
              | .Ok sharedState varstore =>
                  match s₀.sharedState.accountMap.find? address with
                    | .none => 
                      buildContractCallEmptyReturnState s₀ .none ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                    | .some yulContract =>
                      let executionEnv₁ := { sharedState.executionEnv with
                                                calldata := calldata₁,
                                                code := yulContract.code,
                                                codeOwner := s₀.executionEnv.codeOwner
                                                depth := s₀.executionEnv.depth + 1
                                            }
                      let sharedState₁ := { sharedState with
                                              executionEnv := executionEnv₁,
                                              memory := ByteArray.mk #[]
                                          }
                      let s₁ : State := .Ok sharedState₁ default
                      
                      match callDispatcher fuel₁ yulContract.code s₁ with
                        | .error (.YulHalt s₂ _) =>
                        let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                        match s₂ with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₂ _ =>
                            -- Restore ExecutionEnv
                            let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                            let sharedState₃ := { sharedState₂ with
                                                    memory := memory₃,
                                                    returnData := s₂.toMachineState.H_return,
                                                    H_return := ByteArray.empty,
                                                    executionEnv := executionEnv₃
                                                }
                            .ok (.Ok sharedState₃ varstore, [⟨1⟩])
                        | .error e => .error e
                        | .ok (s₂, _) =>                        
                        let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                        match s₂ with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₂ _ =>
                            -- Restore ExecutionEnv
                            let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                            let sharedState₃ := { sharedState₂ with
                                                    memory := memory₃,
                                                    returnData := s₂.toMachineState.H_return,
                                                    H_return := ByteArray.empty,
                                                    executionEnv := executionEnv₃
                                                }
                            .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | _ => match step prim .none s₀ args with
              | .ok (s, lit) => .ok (s, lit.toList)
              | .error e => .error e

  def evalTail (fuel : Nat) (args : List Expr) (codeOverride : Option YulContract) : Except Yul.Exception (State × Literal) → Except Yul.Exception (State × List Literal)
    | .ok (s, arg) => 
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => cons' arg (evalArgs fuel' args codeOverride s)
    | .error e => .error e

  /--
    `evalArgs` evaluates a list of arguments.
  -/
  def evalArgs (fuel : Nat) (args : List Expr) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match args with
        | [] => .ok (s, [])
        | arg :: args =>
          evalTail fuel' args codeOverride (eval fuel' arg codeOverride s)

  /--
    `call` executes a call of a user-defined function.
    
    Intended for use when a contract is calling one of its own functions, rather than an external contract.
  -/
  def call (fuel : Nat) (args : List Literal) (yulFunctionNameOption : Option YulFunctionName) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
        match s.sharedState.accountMap.find? s.executionEnv.codeOwner with
        | .none => .error (.MissingContract (s!"{s.executionEnv.codeOwner}")) 
        | .some yulContract =>
          let code : YulContract := codeOverride.getD yulContract.code
          
          let fOpt : Option FunctionDefinition :=
            match yulFunctionNameOption with
              | .none => .some (FunctionDefinition.Def [] [] [code.dispatcher])
              | .some yulFunctionName =>
                  code.functions.lookup yulFunctionName
          match fOpt with
          | .none => .error (.MissingContractFunction (yulFunctionNameOption.getD ".none"))
          | .some f =>
            let s₁ := 👌 s.initcall f.params args
            match exec fuel' (.Block f.body) codeOverride s₁ with
              | .error e => .error e
              | .ok s₂ =>
                let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
                .ok (s₃, List.map s₂.lookup! f.rets)

  /--
    `callDispatcher` calls the dispatcher of an external contract.
    
    It expects the `calldata` and `code` to be appropriately set.
  -/
  def callDispatcher (fuel : Nat) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
          let f := FunctionDefinition.Def [] [] [s.executionEnv.code.dispatcher]
          let s₁ := 👌 s.initcall f.params []
          match exec fuel' (.Block f.body) codeOverride s₁ with
          | .error e => .error e
          | .ok s₂ =>
            let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
            .ok (s₃, List.map s₂.lookup! f.rets)

  -- Safe to call `List.head!` on return values, because the compiler throws an
  -- error when coarity is > 0 in (1) and when coarity is > 1 in all other
  -- cases.

  def evalPrimCall (fuel : ℕ) (prim : PrimOp) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) => head' (primCall fuel s prim args)
    | .error e => .error e

  def evalCall (fuel : Nat) (f : YulFunctionName) (codeOverride : Option YulContract) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => head' (call fuel' args f codeOverride s)
    | .error e => .error e

  def execPrimCall (fuel : ℕ) (prim : PrimOp) (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) => multifill' vars (primCall fuel s prim args)
    | .error e => .error e

  def execCall (fuel : Nat) (yulFunctionName : YulFunctionName) (vars : List Identifier) (codeOverride : Option YulContract) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => multifill' vars (call fuel' args yulFunctionName codeOverride s)
    | .error e => .error e

  /--
    `execSwitchCases` executes each case of a `switch` statement.
  -/
  def execSwitchCases (fuel : Nat) (codeOverride : Option YulContract) (s : State) : List (Literal × List Stmt) → Except Yul.Exception (List (Literal × (Except Yul.Exception State)))
    | [] => .ok []
    | ((val, stmts) :: cases') =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => 
        match exec fuel' (.Block stmts) codeOverride s with
          | .error (.YulHalt s₂ v) =>
            match execSwitchCases fuel' codeOverride s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .error (.YulHalt s₂ v)) :: s₃)
          | .error e =>
              match execSwitchCases fuel' codeOverride s cases' with
              | .error e => .error e
              | .ok s₃ =>
                .ok ((val, .error e) :: s₃)
          | .ok s₂ =>
            match execSwitchCases fuel' codeOverride s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .ok s₂) :: s₃)

  /--
    `eval` evaluates an expression.

    - calls evaluated here are assumed to have coarity 1
  -/
  def eval (fuel : Nat) (expr : Expr) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception (State × Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
        match expr with

        -- We hit these two cases (`PrimCall` and `Call`) when evaluating:
        --
        --  1. f()                 (expression statements)
        --  2. g(f())              (calls in function arguments)
        --  3. if f() {...}        (if conditions)
        --  4. for {...} f() ...   (for conditions)
        --  5. switch f() ...      (switch conditions)

        | .Call (Sum.inl prim) args => evalPrimCall fuel' prim (reverse' (evalArgs fuel' args.reverse codeOverride s))
        | .Call (Sum.inr yulFunctionName) args        =>
          evalCall fuel' yulFunctionName codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
        | .Var id             => .ok (s, s[id]!)
        | .Lit val            => .ok (s, val)

  /--
    `exec` executs a single statement.
  -/
  def exec (fuel : Nat) (stmt : Stmt) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match stmt with
        | .Block [] => .ok s
        | .Block (stmt :: stmts) =>
          let s₁ := exec fuel' stmt codeOverride s
          match s₁ with
            | .error e => .error e
            | .ok s₁ => exec fuel' (.Block stmts) codeOverride s₁

        | .Let vars exprOption =>
            match exprOption with
              | .none => .ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars)
              | .some expr =>
                match expr with
                  | .Call (Sum.inl prim) args =>
                    execPrimCall fuel' prim vars (reverse' (evalArgs fuel' args.reverse codeOverride s))
                  | .Call (Sum.inr yulFunctionName) args =>
                    execCall fuel' yulFunctionName vars codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
                  | .Var identifier => .ok (s.insert vars.head! s[identifier]!) -- It should be safe to call head! here if the Yul code is parsed correctly.
                  | .Lit literal => .ok (s.insert vars.head! literal) -- It should be safe to call head! here if the Yul code is parsed correctly.

        | .If cond body =>
          match eval fuel' cond codeOverride s with
            | .error e => .error e
            | .ok (s, cond) =>
              if cond ≠ ⟨0⟩ then exec fuel' (.Block body) codeOverride s else .ok s

        -- "Expressions that are also statements (i.e. at the block level) have
        -- to evaluate to zero values."
        --
        -- (https://docs.soliditylang.org/en/latest/yul.html#restrictions-on-the-grammar)
        --
        -- Thus, we cannot have literals or variables on the RHS.
        | .ExprStmtCall expr =>
             match expr with
               | .Call (Sum.inl prim) args => execPrimCall fuel' prim [] (reverse' (evalArgs fuel' args.reverse codeOverride s))
               | .Call (Sum.inr f) args => execCall fuel' f [] codeOverride (reverse' (evalArgs fuel' args.reverse codeOverride s))
               | _ => .error .InvalidExpression -- This case should never occur because we cannot have literals or variables on the RHS, as noted above.

        | .Switch cond cases' default' =>
          match eval fuel' cond codeOverride s with
            | .error e => .error e
            | .ok (s₁, cond) =>
              match execSwitchCases fuel' codeOverride s₁ cases' with
              | .error e => .error e  
              | .ok branches =>
                match exec fuel' (.Block default') codeOverride s₁ with
                | .error e => .error e
                | .ok s₂ =>
                  (List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) (.ok s₂) branches)

        -- A `Break` or `Continue` in the pre or post is a compiler error,
        -- so we assume it can't happen and don't modify the state in these
        -- cases. (https://docs.soliditylang.org/en/v0.8.23/yul.html#loops)
        | .For cond post body => (loop fuel' cond post body codeOverride s)
        | .Continue => .ok (🔁 s)
        | .Break => .ok (💔 s)
        | .Leave => .ok (🚪 s)

  /--
    `loop` executes a for-loop.
  -/
  def loop (fuel : Nat) (cond : Expr) (post body : List Stmt) (codeOverride : Option YulContract) (s : State) : Except Yul.Exception State :=
    match fuel with
      | 0 => .error .OutOfFuel
      | 1 => .error .OutOfFuel
      | fuel' + 1 + 1 =>
        match eval fuel' cond codeOverride (👌s) with
        | .error e => .error e
        | .ok (s₁, x) =>
          if x = ⟨0⟩
            then .ok (s₁✏️⟦s⟧?)
            else
              match exec fuel' (.Block body) codeOverride s₁ with
              | .error e => .error e
              | .ok s₂ =>
                match s₂ with
                  | .OutOfFuel                      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Break _ _)      => .ok (🧟s₂✏️⟦s⟧?)
                  | .Checkpoint (.Leave _ _)      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Continue _ _)
                  | _ =>
                    match exec fuel' (.Block post) codeOverride (🧟 s₂) with
                    | .error e => .error e
                    | .ok s₃ =>
                      let s₄ := s₃✏️⟦s⟧?
                      match exec fuel' (.For cond post body) codeOverride s₄ with
                      | .error e => .error e
                      | .ok s₅ =>
                        let s₆ := s₅✏️⟦s⟧?
                        .ok s₆
end

def execTopLevel (fuel : Nat) (stmt : Stmt) (s : State) : State :=
  match exec fuel stmt .none s with
    | .error .InvalidArguments => default
    | .error .NotEncodableRLP => default
    | .error .InvalidInstruction => default
    | .error .OutOfFuel => default
    | .error .StaticModeViolation => s -- Revert, note that we do not model charging gas in the Yul semantics
    | .error (.MissingContract _) => default
    | .error (.MissingContractFunction _) => default -- We do not model fallback functions
    | .error .InvalidExpression => default
    | .error .YulEXTCODESIZENotImplemented => default
    | .error .Revert => s
    | .error (.YulHalt s _) => s
    | .ok s => s

notation "🍄" => exec
notation "🌸" => eval

end Yul

end EvmYul

```
`EvmYul/Yul/MachineState.lean`:

```lean
import EvmYul.MachineState
import EvmYul.Yul.Wheels

namespace EvmYul

namespace Yul

/--
The partial Yul `MachineState` `μ`.
-/
structure MachineState extends EvmYul.MachineState where
  varStore : VarStore
deriving Inhabited

end Yul

end EvmYul

```
`EvmYul/Yul/PrimOps.lean`:

```lean
import EvmYul.Yul.State
import EvmYul.Yul.Exception
import EvmYul.Yul.StateOps
import EvmYul.SharedStateOps

import EvmYul.UInt256

import EvmYul.Wheels

namespace EvmYul

namespace Yul

open Lean Parser

set_option autoImplicit true

def Transformer := Yul.State → List Literal → Except Yul.Exception (Yul.State × Option Literal)

def execUnOp (f : Primop.Unary) : Transformer
  | s, [a] => .ok (s, f a)
  | _, _   => throw .InvalidArguments

def execBinOp (f : Primop.Binary) : Transformer
  | s, [a, b] => .ok (s, f a b)
  | _, _      => throw .InvalidArguments

def execTriOp (f : Primop.Ternary) : Transformer
  | s, [a, b, c] => .ok (s, f a b c)
  | _, _         => throw .InvalidArguments

def execQuadOp (f : Primop.Quaternary) : Transformer
  | s, [a, b, c, d] => .ok (s, f a b c d)
  | _, _            => throw .InvalidArguments

def executionEnvOp (op : ExecutionEnv .Yul → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.executionEnv)

def unaryExecutionEnvOp (op : ExecutionEnv .Yul → UInt256 → UInt256) : Transformer :=
  λ yulState lits ↦
    match lits with
    | [a] => .ok (yulState, .some <| op yulState.executionEnv a)
    | _ => .error .InvalidArguments

def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toMachineState)

def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let mState' := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let (val, mState') := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', some val)
    | _ => .error .InvalidArguments

def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let mState' := op yulState.toMachineState a b c
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def binaryStateOp
  (op : EvmYul.State .Yul → UInt256 → UInt256 → EvmYul.State .Yul) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let state' := op yulState.toState a b
      let yulState' := yulState.setState state'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

def stateOp (op : EvmYul.State .Yul → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toState)

def unaryStateOp (op : EvmYul.State .Yul → UInt256 → EvmYul.State .Yul × UInt256) : Transformer :=
  λ yulState lits ↦
      match lits with
        | [lit] =>
          let (state', b) := op yulState.toState lit
          let yulState' :=
            yulState.setSharedState { yulState.toSharedState with toState := state' }
          .ok (yulState', some b)
        | _ => .error .InvalidArguments

def ternaryCopyOp (op : SharedState .Yul → UInt256 → UInt256 → UInt256 → SharedState .Yul) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let sState' := op yulState.toSharedState a b c
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

def quaternaryCopyOp
  (op : SharedState .Yul → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .Yul) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c, d] =>
      let sState' := op yulState.toSharedState a b c d
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

private def yulLogOp (yulState : State) (a b : UInt256) (t : Array UInt256) : State × Option Literal :=
  let sharedState' := SharedState.logOp a b t yulState.toSharedState
  ( yulState.setSharedState sharedState'
  , none
  )

def log0Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b] =>
        .ok <| yulLogOp yulState a b #[]
      | _ => .ok (yulState, none)

def log1Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c] =>
        .ok <| yulLogOp yulState a b #[c]
      | _ => .ok (yulState, none)

def log2Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d] =>
        .ok <| yulLogOp yulState a b #[c, d]
      | _ => .ok (yulState, none)

def log3Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e] =>
        .ok <| yulLogOp yulState a b #[c, d, e]
      | _ => .ok (yulState, none)

def log4Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e, f] =>
        .ok <| yulLogOp yulState a b #[c, d, e, f]
      | _ => .ok (yulState, none)

end Yul

end EvmYul

```
`EvmYul/Yul/SizeLemmas.lean`:

```lean
import EvmYul.Yul.Ast

namespace EvmYul

namespace Yul

namespace SizeLemmas

section

open EvmYul Ast Expr Stmt FunctionDefinition

variable {expr arg : Expr}
         {stmt : Stmt}
         {exprs args args' : List Expr}
         {stmts : List Stmt}
         {f : FunctionDefinition}
         {fName : YulFunctionName}
         {prim : PrimOp}
         {α : Type}
         {xs ys : List α}

-- ============================================================================
--  SIZEOF LEMMAS
-- ============================================================================

@[simp]
lemma Zero.zero_le {n : ℕ} : Zero.zero ≤ n := by ring_nf; exact Nat.zero_le _

@[simp]
lemma List.zero_lt_sizeOf : 0 < sizeOf xs
:= by
  rcases xs <;> simp

@[simp]
lemma List.reverseAux_size : sizeOf (List.reverseAux args args') = sizeOf args + sizeOf args' - 1 := by
  induction args generalizing args' with
    | nil => simp
    | cons z zs ih =>
      aesop (config := {warnOnNonterminal := false}); omega

@[simp]
lemma List.reverse_size : sizeOf (args.reverse) = sizeOf args := by
  unfold List.reverse
  rw [List.reverseAux_size]
  simp

/--
  Expressions have positive size.
-/ 
@[simp]
lemma Expr.zero_lt_sizeOf : 0 < sizeOf expr := by
  rcases expr <;> simp

@[simp]
lemma Stmt.sizeOf_stmt_ne_0 : sizeOf stmt ≠ 0 := by cases stmt <;> aesop

/--
  Statements have positive size.
-/
@[simp]
lemma Stmt.zero_lt_sizeOf : 0 < sizeOf stmt := by
  have : sizeOf stmt ≠ 0 := by simp
  omega

/--
  Lists of expressions have positive size.
-/
@[simp]
lemma Expr.zero_lt_sizeOf_List : 0 < sizeOf exprs := by
  have : sizeOf exprs ≠ 0 := by cases exprs <;> aesop
  omega

@[simp]
lemma Expr.sizeOf_head_lt_sizeOf_List : sizeOf expr < sizeOf (expr :: exprs) := by
  simp +arith

@[simp]
lemma Expr.sizeOf_tail_lt_sizeOf_List : sizeOf exprs < sizeOf (expr :: exprs) := by
  simp

/--
  Lists of statements have positive size.
-/
@[simp]
lemma Stmt.zero_lt_sizeOf_List : 0 < sizeOf stmts := by cases stmts <;> aesop

/--
  Function definitions have positive size.
-/
@[simp]
lemma FunctionDefinition.zero_lt_sizeOf : 0 < sizeOf f := by cases f; aesop

@[simp]
lemma Expr.sizeOf_args_lt_sizeOf_Call : sizeOf args < sizeOf (Call (Sum.inr fName) args) := by
  simp

@[simp]
lemma Expr.sizeOf_args_lt_sizeOf_PrimCall : sizeOf args < sizeOf (Call (Sum.inl prim) args) := by
  simp

/--
  The size of the body of a function is less than the size of the function itself.
-/
@[simp]
lemma FunctionDefinition.sizeOf_body_lt_sizeOf : sizeOf (body f) < sizeOf f := by unfold body; aesop

lemma FunctionDefinition.sizeOf_body_succ_lt_sizeOf : sizeOf (FunctionDefinition.body f) + 1 < sizeOf f := by
  cases f
  unfold body
  simp +arith
  exact le_add_right List.zero_lt_sizeOf

/--
  The size of the head of a list of statements is less than the size of a block containing the whole list.
-/
@[simp]
lemma Stmt.sizeOf_head_lt_sizeOf : sizeOf stmt < sizeOf (Block (stmt :: stmts)) := by
  simp only [Block.sizeOf_spec, List.cons.sizeOf_spec]
  linarith

/--
  The size of the head of a list of statements is less than the size of a block containing the whole list.
-/
@[simp]
lemma Stmt.sizeOf_head_lt_sizeOf_tail : sizeOf (Block stmts) < sizeOf (Block (stmt :: stmts)) := by simp

end

end SizeLemmas

end Yul

end EvmYul

```
`EvmYul/Yul/State.lean`:

```lean
import Mathlib.Data.Finmap

import EvmYul.Wheels
import EvmYul.Yul.Wheels
import EvmYul.SharedState

namespace EvmYul

namespace Yul

/--
A jump in control flow containing a checkpoint of the state at jump-time.
- `Continue`: yul `continue` was encountered
- `Break`   : yul `break` was encountered
- `Leave`   : evm `return` was encountered
-/
inductive Jump where
  | Continue : EvmYul.SharedState .Yul → VarStore → Jump
  | Break    : EvmYul.SharedState .Yul → VarStore → Jump
  | Leave    : EvmYul.SharedState .Yul → VarStore → Jump

/--
The Yul `State`.
- `Ok state varstore` : The underlying `EvmYul.State` `state` along with `varstore`.
- `OutOfFuel`         : No state.
- `Checkpoint`        : Restore a previous state due to control flow.

The definition is ever so slightly off due to historical reasons.
-/
inductive State where
  | Ok         : EvmYul.SharedState .Yul → VarStore → State
  | OutOfFuel  : State
  | Checkpoint : Jump → State

instance : Inhabited State where
  default := .Ok default default

namespace State

def sharedState : State → EvmYul.SharedState .Yul
  | Ok sharedState _ => sharedState
  | _ => default

end State

end Yul

end EvmYul

```
`EvmYul/Yul/StateOps.lean`:

```lean
import EvmYul.Yul.State

namespace EvmYul

namespace Yul

namespace State

-- | Insert an (identifier, literal) pair into the varstore.
def insert (var : Identifier) (val : Literal) : Yul.State → Yul.State
  | (Ok sharedState store) => Ok sharedState (store.insert var val)
  | s => s

-- | Zip a list of variables with a list of literals and insert right-to-left.
def multifill (vars : List Identifier) (vals : List Literal) : Yul.State → Yul.State
  | s@(Ok _ _) => (List.zip vars vals).foldr (λ (var, val) s ↦ s.insert var val) s
  | s => s

-- | Overwrite the EvmYul.Yul.State state of some state.
def setSharedState (sharedState : EvmYul.SharedState .Yul) : Yul.State → Yul.State
  | Ok _ store => Ok sharedState store
  | s => s

def setMachineState (mstate : EvmYul.MachineState) : Yul.State → Yul.State
  | Ok sstate store => Ok {sstate with toMachineState := mstate} store
  | s => s

def setState (state : EvmYul.State .Yul) : Yul.State → Yul.State
  | Ok sstate store => Ok {sstate with toState := state} store
  | s => s

-- | Overwrite the varstore of some state.
def setStore (s s' : Yul.State) : Yul.State :=
  match s, s' with
    | (Ok sharedState _), (Ok _ store) => Ok sharedState store
    | s, _ => s

def setContinue : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Continue sharedState store)
  | s => s

def setBreak : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Break sharedState store)
  | s => s

def setLeave : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Leave sharedState store)
  | s => s

-- | Indicate that we've hit an infinite loop/ran out of fuel.
def diverge : Yul.State → Yul.State
  | Ok _ _ => .OutOfFuel
  | s => s

-- | Initialize function parameters and return values in varstore.
def initcall (params : List Identifier) (args : List Literal) : Yul.State → Yul.State
  | s@(Ok _ _) =>
    let s₁ := s.setStore default
    s₁.multifill params args
  | s => s

-- | Since it literally does not matter what happens if the state is non-Ok, we just use the default.
def mkOk : Yul.State → Yul.State
  | Checkpoint _ => default
  | s => s

-- | Helper function for `reviveJump`.
def revive : Jump → Yul.State
  | .Continue sharedState store => Ok sharedState store
  | .Break sharedState store => Ok sharedState store
  | .Leave sharedState store => Ok sharedState store

-- | Revive a saved state (sharedState, varstore), discarding top-level (sharedState, varstore).
--
-- Called after we've finished executing:
--    * A loop
--    * A function call
--
-- The compiler disallows top-level `Continue`s or `Break`s in function bodies,
-- thus it is safe to assume the state we're reviving is a checkpoint from the
-- expected flavor of `Jump`.
def reviveJump : Yul.State → Yul.State
  | Checkpoint c => revive c
  | s => s

-- | If s' is non-Ok, overwrite s with s'.
def overwrite? (s s' : Yul.State) : Yul.State :=
  match s' with
    | Ok _ _ => s
    | _ => s'

-- ============================================================================
--  STATE QUERIES
-- ============================================================================

-- | Lookup the literal associated with an variable in the varstore, returning 0 if not found.
def lookup! (var : Identifier) : Yul.State → Literal
  | Ok _ store => (store.lookup var).get!
  | Checkpoint (.Continue _ store) => (store.lookup var).get!
  | Checkpoint (.Break _ store) => (store.lookup var).get!
  | Checkpoint (.Leave _ store) => (store.lookup var).get!
  | _ => ⟨0⟩

-- ============================================================================
--  STATE NOTATION
-- ============================================================================

def toSharedState : State → EvmYul.SharedState .Yul
  | Ok s _ => s
  | _ => default

def executionEnv : State → EvmYul.ExecutionEnv .Yul
  | Ok s _ => s.executionEnv
  | _ => default

def toMachineState : State → EvmYul.MachineState
  | Ok s _ => s.toMachineState
  | _ => default

def toState : State → EvmYul.State .Yul
  | Ok s _ => s.toState
  | _ => default

def store : State → VarStore
  | Ok _ store => store
  | _ => default

-- | All state-related functions should be prefix operators so they can be read right-to-left.

-- Yul.State queries
-- notation:65 s:64"[" var "]!" => Yul.State.lookup! var s

/--
TODO - The notation is a bit of a remnant from EvmYul and it is unnecessarily overzaelous.
This should have been an instance of GetElem in the first place.

N.B. We also ignore the validity condition altogether for the time being.
-/
instance : GetElem Yul.State Identifier Literal (λ s idx ↦ idx ∈ s.store) where
  getElem s ident _ := s.lookup! ident

notation "❓" => Yul.State.isOutOfFuel

-- Yul.State transformers
notation:65 s:64 "⟦" var "↦" lit "⟧" => Yul.State.insert var lit s
notation:65 "🔁" s:64 => Yul.State.setContinue s
notation:65 "💔" s:64 => Yul.State.setBreak s
notation:65 "🚪" s:64 => Yul.State.setLeave s
notation:65 s:64 "🏪⟦" s' "⟧" => Yul.State.setStore s s'
notation:65 s:64 "🇪⟦" sharedState "⟧" => Yul.State.setSharedState sharedState s
notation:65 "🪫" s:64 => Yul.State.diverge s
notation:65 "👌" s:64 => Yul.State.mkOk s
notation:65 s:64 "☎️⟦" params "," args "⟧" => Yul.State.initcall params args s
notation:65 s:64 "✏️⟦" s' "⟧?"  => Yul.State.overwrite? s s'
notation:64 (priority := high) "🧟" s:max => Yul.State.reviveJump s

end State

end Yul

end EvmYul

```
`EvmYul/Yul/Wheels.lean`:

```lean
import Mathlib.Data.Finmap

import EvmYul.Wheels

namespace EvmYul

namespace Yul

abbrev VarStore := Finmap (λ _ : Identifier ↦ Literal)

end Yul

end EvmYul

```
`EvmYul/Yul/YulNotation.lean`:

```lean
import EvmYul.Yul.Ast
import Lean.Parser
import EvmYul.Operations

namespace EvmYul

namespace Yul

namespace Notation

open Ast Lean Parser Elab Term

def yulKeywords := ["let", "if", "default", "switch", "case"]

def idFirstChar : Array Char := Id.run <| do
  let mut arr := #[]
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('a'.toNat + i))
  for i in [0:26] do
    arr := arr.push (Char.ofNat ('A'.toNat + i))
  arr := (arr.push '_').push '$'
  return arr

def idSubsequentChar : Array Char := Id.run <| do
  let mut arr := idFirstChar
  for i in [0:10] do
    arr := arr.push (Char.ofNat ('0'.toNat + i))
  return arr.push '.'

def idFn : ParserFn := fun c s => Id.run do
  let input := c.input
  let start := s.pos
  if h : input.atEnd start then
    s.mkEOIError
  else
    let fst := input.get' start h
    if not (idFirstChar.contains fst) then
      return s.mkError "yul identifier"
    let s := takeWhileFn idSubsequentChar.contains c (s.next input start)
    let stop := s.pos
    let name := .str .anonymous (input.extract start stop)
    if yulKeywords.contains name.lastComponentAsString then
      return s.mkError "yul identifier"
    mkIdResult start none name c s

def idNoAntiquot : Parser := { fn := idFn }

section
open PrettyPrinter Parenthesizer Syntax.MonadTraverser Formatter

@[combinator_formatter idNoAntiquot]
def idNoAntiquot.formatter : Formatter := do
  Formatter.checkKind identKind
  let Syntax.ident info _ idn _ ← getCur
    | throwError m!"not an ident: {← getCur}"
  Formatter.pushToken info idn.toString true
  goLeft

@[combinator_parenthesizer idNoAntiquot]
def idNoAntiquot.parenthesizer := Parenthesizer.visitToken
end

@[run_parser_attribute_hooks]
def ident : Parser := withAntiquot (mkAntiquot "ident" identKind) idNoAntiquot

declare_syntax_cat expr
declare_syntax_cat stmt

syntax identifier_list := ident,*
syntax typed_identifier_list := ident,*
syntax function_call := ident "(" expr,* ")"
syntax block := "{" stmt* "}"
syntax if' := "if" expr block
syntax function_definition :=
  "function" ident "(" typed_identifier_list ")"
    ("->" typed_identifier_list)?
    block
syntax params_list := "[" typed_identifier_list "]"
syntax variable_declaration := "let" ident (":=" expr)?
-- syntax let_str_literal := "let" ident ":=" str -- TODO(fix)
syntax variable_declarations := "let" typed_identifier_list (":=" expr)?
syntax for_loop := "for" block expr block block
syntax assignment := identifier_list ":=" expr

syntax stmtlist := stmt*

syntax block : stmt
syntax if' : stmt
syntax function_definition : stmt
syntax variable_declarations : stmt
syntax assignment : stmt
syntax expr : stmt
-- syntax let_str_literal : stmt -- TODO(fix)
syntax for_loop : stmt
syntax "break" : stmt
syntax "continue" : stmt
syntax "leave" : stmt

syntax ident : expr
syntax numLit : expr
syntax function_call: expr

syntax default := "default" "{" stmt* "}"
syntax case := "case" expr "{" stmt* "}"
syntax switch := "switch" expr case+ (default)?
syntax switch_default := "switch" expr default

syntax switch : stmt
syntax switch_default : stmt

scoped syntax:max "<<" expr ">>" : term
scoped syntax:max "<f" function_definition ">" : term
scoped syntax:max "<s" stmt ">" : term
scoped syntax:max "<ss" stmt ">" : term
scoped syntax:max "<params" params_list ">" : term

def translateString (s : String) : TermElabM Term := 
  pure (Syntax.mkStrLit s)

partial def translatePrimOp (primOp : PrimOp) : TermElabM Term := do
  let (family, instr) ← familyAndInstr primOp
  PrettyPrinter.delab (
    ←Lean.Meta.mkAppM
      family.toName
      #[←Lean.Meta.mkAppOptM instr.toName #[mkConst YulTag]]
  )
  where
    familyAndInstr (primOp : PrimOp) : TermElabM (String × String) := do
      let family :: instr :: [] := toString primOp |>.splitOn | throwError s!"{primOp} shape not <family> <instruction>"
      pure (family, instr.drop 1 |>.dropRight 1)
    YulTag : Name := "EvmYul.OperationType.Yul".toName

partial def translateIdent (idn : TSyntax `ident) : TSyntax `term :=
  Syntax.mkStrLit idn.getId.lastComponentAsString

def parseFunction : String → PrimOp ⊕ Identifier
  | "add" => .inl .ADD
  | "sub" => .inl .SUB
  | "mul" => .inl .MUL
  | "div" => .inl .DIV
  | "sdiv" => .inl .SDIV
  | "mod" => .inl .MOD
  | "smod" => .inl .SMOD
  | "addmod" => .inl .ADDMOD
  | "mulmod" => .inl .MULMOD
  | "exp" => .inl .EXP
  | "signextend" => .inl .SIGNEXTEND
  | "lt" => .inl .LT
  | "gt" => .inl .GT
  | "slt" => .inl .SLT
  | "sgt" => .inl .SGT
  | "eq" => .inl .EQ
  | "iszero" => .inl .ISZERO
  | "and" => .inl .AND
  | "or" => .inl .OR
  | "xor" => .inl .XOR
  | "not" => .inl .NOT
  | "byte" => .inl .BYTE
  | "shl" => .inl .SHL
  | "shr" => .inl .SHR
  | "sar" => .inl .SAR
  | "keccak256" => .inl .KECCAK256
  | "address" => .inl .ADDRESS
  | "balance" => .inl .BALANCE
  | "origin" => .inl .ORIGIN
  | "caller" => .inl .CALLER
  | "callvalue" => .inl .CALLVALUE
  | "calldataload" => .inl .CALLDATALOAD
  | "calldatacopy" => .inl .CALLDATACOPY
  | "calldatasize" => .inl .CALLDATASIZE
  | "codesize" => .inl .CODESIZE
  | "codecopy" => .inl .CODECOPY
  | "gasprice" => .inl .GASPRICE
  | "extcodesize" => .inl .EXTCODESIZE
  | "extcodecopy" => .inl .EXTCODECOPY
  | "extcodehash" => .inl .EXTCODEHASH
  | "returndatasize" => .inl .RETURNDATASIZE
  | "returndatacopy" => .inl .RETURNDATACOPY
  | "blockhash" => .inl .BLOCKHASH
  | "coinbase" => .inl .COINBASE
  | "timestamp" => .inl .TIMESTAMP
  | "gaslimit" => .inl .GASLIMIT
  | "chainid" => .inl .CHAINID
  | "selfbalance" => .inl .SELFBALANCE
  | "mload" => .inl .MLOAD
  | "mstore" => .inl .MSTORE
  | "sload" => .inl .SLOAD
  | "sstore" => .inl .SSTORE
  | "msize" => .inl .MSIZE
  | "gas" => .inl .GAS
  | "pop" => .inl .POP
  | "revert" => .inl .REVERT
  | "return" => .inl .RETURN
  | "call" => .inl .CALL
  | "staticcall" => .inl .STATICCALL
  | "delegatecall" => .inl .DELEGATECALL
  | "callcode" => .inl .CALLCODE
  -- | "loadimmutable" => .inl  .LOADI
  -- | "log0" => .inl .LOG0
  | "log1" => .inl .LOG1
  | "log2" => .inl .LOG2
  | "log3" => .inl .LOG3
  | "log4" => .inl .LOG4
  | "number" => .inl .NUMBER
  | userF => .inr userF

partial def translateExpr (expr : TSyntax `expr) : TermElabM Term :=
  match expr with
    | `(expr| $idn:ident) => `(Expr.Var $(translateIdent idn))
    | `(expr| $num:num) => `(Expr.Lit (.ofNat $num))
    | `(expr| $name:ident($args:expr,*)) => do
      let args' ← (args : TSyntaxArray `expr).mapM translateExpr
      let f' := parseFunction (TSyntax.getId name).lastComponentAsString
      match f' with
        | .inl primOp =>
          let primOp ← translatePrimOp primOp
          `(Expr.Call (Sum.inl $primOp) [$args',*])
        | .inr yulFunctionName =>
          let yulFunctionName ← translateString yulFunctionName
          `(Expr.Call (Sum.inr $yulFunctionName) [$args',*])
    | _ => throwError "unknown expr"

partial def translateExpr' (expr : TSyntax `expr) : TermElabM Term :=
  match expr with
  | `(expr| $num:num) => `(.ofNat $num)
  | exp => translateExpr exp

partial def translateParamsList
  (params : TSyntax `EvmYul.Yul.Notation.params_list)
: TermElabM Term :=
  match params with
  | `(params_list| [ $args:ident,* ]) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    `([$args',*])
  | _ => throwError (toString params.raw)

mutual
partial def translateFdef
  (fdef : TSyntax `EvmYul.Yul.Notation.function_definition)
: TermElabM Term :=
  match fdef with
  | `(function_definition| function $_:ident($args:ident,*) {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(EvmYul.Yul.Ast.FunctionDefinition.Def [$args',*] [] [$body',*])
  | `(function_definition| function $_:ident($args:ident,*) -> $rets,* {$body:stmt*}) => do
    let args' := (args : TSyntaxArray _).map translateIdent
    let rets' := (rets : TSyntaxArray _).map translateIdent
    let body' ← body.mapM translateStmt
    `(EvmYul.Yul.Ast.FunctionDefinition.Def [$args',*] [$rets',*] [$body',*])
  | _ => throwError (toString fdef.raw)

partial def translateStmt (stmt : TSyntax `stmt) : TermElabM Term :=
  match stmt with

  -- Block
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `(Stmt.Block ([$stmts',*]))

  -- If
  | `(stmt| if $cond:expr {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let body' ← body.mapM translateStmt
    `(Stmt.If $cond' [$body',*])

  -- Switch
  | `(stmt| switch $expr:expr $[case $lits { $cs:stmt* }]* $[default { $dflts:stmt* }]?) => do
    let expr ← translateExpr expr
    let lits ← lits.mapM translateExpr'
    let cases ← cs.mapM (λ cc ↦ cc.mapM translateStmt)
    let f (litCase : TSyntax `term × Array Term) : TermElabM Term := do
      let (lit, cs) := litCase; `(($lit, [$cs,*]))
    let switchCases ← lits.zip cases |>.mapM f
    let dflt ← match dflts with
                 | .none => `([.Break])
                 | .some dflts => `([$(←dflts.mapM translateStmt),*])
    `(Stmt.Switch $expr [$switchCases,*] $dflt)

  -- Switch
  | `(stmt| switch $expr:expr default {$dflts:stmt*}) => do
    let expr ← translateExpr expr
    let dflt ← dflts.mapM translateStmt
    `(Stmt.Switch $expr [] ([$dflt,*]))

  -- Let
  | `(stmt| let $ids:ident,* := $expr:expr) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let expr ← translateExpr expr
    `(Stmt.Let [$ids',*] (.some $expr))

  -- LetEq
  -- | `(stmt| let $idn:ident := $init:expr) => do
  --   let idn' := translateIdent idn
  --   let expr' ← translateExpr init
  --   `(Stmt.Let [$idn'] (.some $expr'))

  -- TODO(fix)
  -- | `(stmt| let $idn:ident := $s:str) => do
  --   let idn' := translateIdent idn
  --   `(Stmt.LetEq $idn' _)

  -- Let
  | `(stmt| let $ids:ident,*) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    `(Stmt.Let [$ids',*] .none)

  -- AssignCall
  | `(stmt| $ids:ident,* := $expr:expr) => do
    let ids' := (ids : TSyntaxArray _).map translateIdent
    let expr ← translateExpr expr
    `(Stmt.Let [$ids',*] (.some $expr))

  -- ExprStmt
  | `(stmt| $expr:expr) => do
    let expr ← translateExpr expr
    `(Stmt.ExprStmtCall $expr)

  -- For
  | `(stmt| for {} $cond:expr {$post:stmt*} {$body:stmt*}) => do
    let cond' ← translateExpr cond
    let post' ← post.mapM translateStmt
    let body' ← body.mapM translateStmt
    `(Stmt.For $cond' [$post',*] [$body',*])

  -- Break
  | `(stmt| break) => `(Stmt.Break)

  -- Continue
  | `(stmt| continue) => `(Stmt.Continue)

  -- Leave
  | `(stmt| leave) => `(Stmt.Leave)

  -- Anything else
  | _ => throwError (toString stmt.raw)
end

partial def translateStmtList (stmt : TSyntax `stmt) : TermElabM Term :=
  match stmt with
  | `(stmt| {$stmts:stmt*}) => do
    let stmts' ← stmts.mapM translateStmt
    `([$stmts',*])
  | _ => throwError (toString stmt.raw)

private def elabWith {β : SyntaxNodeKinds}
  (x : Syntax) (translator : TSyntax β → TermElabM Term) : TermElabM Lean.Expr := do
  elabTerm (←translator (TSyntax.mk (ks := β) x)) .none

elab "<<" e:expr ">>"               : term => elabWith e translateExpr
elab "<f" f:function_definition ">" : term => elabWith f translateFdef
elab "<s" s:stmt ">"                : term => elabWith s translateStmt
elab "<ss" ss:stmt ">"              : term => elabWith ss translateStmtList
elab "<params" p:params_list ">"    : term => elabWith p translateParamsList

def f : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>

example : <<f(42)>> = (.Call (Sum.inr "f") [Expr.Lit ⟨42⟩]) := rfl
example : <params [a,b,c] > = ["a", "b", "c"] := rfl
example : << bar >> = Expr.Var "bar" := rfl
example : << 42 >> = Expr.Lit ⟨42⟩ := rfl
example : <s break > = Stmt.Break := rfl
example : <s let a, b := f(42) > = Stmt.Let ["a", "b"] (.some (.Call (Sum.inr "f") [Expr.Lit ⟨42⟩])) := rfl
example : <s let a > = Stmt.Let ["a"] .none := rfl
example : <s let a := 5 > = Stmt.Let ["a"] (.some (.Lit ⟨5⟩)) := rfl
example : <s a, b := f(42) > = Stmt.Let ["a", "b"] (.some (.Call (Sum.inr "f") [Expr.Lit ⟨42⟩])) := rfl
example : <s a := 42 > = Stmt.Let ["a"] (.some (.Lit ⟨42⟩)) := rfl

example : <s c := add(a, b) > = Stmt.Let ["c"] (.some (Expr.Call (Sum.inl (Operation.StopArith Operation.SAOp.ADD)) [Expr.Var "a", Expr.Var "b"])) := rfl
example : <s let c := sub(a, b) > = Stmt.Let ["c"] (.some (Expr.Call (Sum.inl (Operation.StopArith Operation.SAOp.SUB)) [Expr.Var "a", Expr.Var "b"])) := rfl
example : <s let a := 5 > = Stmt.Let ["a"] (.some (.Lit ⟨5⟩)) := rfl
example : <s {} >
  = Stmt.Block [] := rfl
example : <s
{
  break
  let a := 5
  break
}
> = Stmt.Block [<s break>, <s let a := 5>, <s break>] := rfl
example : <s
  if a {
    let b := 5
    break
  }
> = Stmt.If <<a>> [<s let b := 5>, <s break >] := rfl

example : <ss {
  let a
  let b
  let c
} > = [<s let a>, <s let b>, <s let c>] := rfl

example : <s for {} 0 {} {} > = Stmt.For (.Lit ⟨0⟩) [] [] := by rfl

example : <<
  add(1, 1)
  >> = Expr.Call (Sum.inl (Operation.StopArith Operation.SAOp.ADD)) [Expr.Lit ⟨1⟩, Expr.Lit ⟨1⟩] := rfl

example : <s
  for {} lt(i, exponent) { i := add(i, 1) }
  {
    result := mul(result, base)
  }
> = Stmt.For <<lt(i, exponent)>> [<s i := add(i, 1)>]
      [<s result := mul(result, base)>] := rfl

def sort2 : FunctionDefinition := <f
  function sort2(a, b) -> x, y {
    if lt(a, b) {
      x := a
      y := b
      leave
    }
    x := b
    y := a
  }
>

def no_rets : FunctionDefinition := <f
  function no_rets(a, b) {
  }
>

example : <s
  switch a
  case 42 { continue }
  default { break }
> = Stmt.Switch (Expr.Var "a") [(⟨42⟩, [.Continue])] [.Break] := rfl

example : <s let a, b, c > = Stmt.Let ["a", "b", "c"] .none := rfl
example : <s revert(0, 0) > = Stmt.ExprStmtCall (.Call (Sum.inl (.System (.REVERT))) [(Expr.Lit ⟨0⟩), (Expr.Lit ⟨0⟩)]) := rfl
example : <s if 1 { leave } > = Stmt.If (.Lit ⟨1⟩) [Stmt.Leave] := rfl
example : <s {
    if 1 { leave }
    leave
  }
> = Stmt.Block [Stmt.If (.Lit ⟨1⟩) [.Leave], .Leave] := rfl

end Notation

end Yul

end EvmYul

```
`EvmYul/Yul/YulSemanticsTests/Caller.sol`:

```sol
pragma solidity ^0.8.30;

interface StorageContract {
    function store(uint256 num) external;
    function retrieve() external returns (uint256);
}

contract CallerContract {

    uint256 number;

    function testStoreAndRetrieveExternal(uint256 v) public {
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        StorageContract c = StorageContract(storageContractAddr);
        c.store(v);
        number = c.retrieve();
    }

}
```
`EvmYul/Yul/YulSemanticsTests/Caller.yul`:

```yul
Optimized IR:
/// @use-src 0:"Caller.sol"
object "CallerContract_47" {
    code {
        {
            /// @src 0:151:488  "contract CallerContract {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("CallerContract_47_deployed")
            codecopy(_1, dataoffset("CallerContract_47_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Caller.sol"
    object "CallerContract_47_deployed" {
        code {
            {
                /// @src 0:151:488  "contract CallerContract {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x5ec1cee6, shr(224, calldataload(0)))
                    {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            /// @ast-id 46 @src 0:203:485  "function testStoreAndRetrieveExternal(uint256 v) public {..."
            function fun_testStoreAndRetrieveExternal(var_v)
            {
                /// @src 0:437:447  "c.store(v)"
                let _1 := extcodesize(/** @src 0:151:488  "contract CallerContract {..." */ 2)
                /// @src 0:437:447  "c.store(v)"
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 := /** @src 0:151:488  "contract CallerContract {..." */ mload(64)
                /// @src 0:437:447  "c.store(v)"
                mstore(_2, /** @src 0:151:488  "contract CallerContract {..." */ shl(224, 0x6057361d))
                /// @src 0:437:447  "c.store(v)"
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4, /** @src 0:151:488  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                /// @src 0:466:478  "c.retrieve()"
                let _7 := /** @src 0:151:488  "contract CallerContract {..." */ mload(64)
                /// @src 0:466:478  "c.retrieve()"
                mstore(_7, /** @src 0:151:488  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:466:478  "c.retrieve()"
                let _8 := add(_7, /** @src 0:437:447  "c.store(v)" */ 4)
                /// @src 0:466:478  "c.retrieve()"
                let _9 := gas()
                let _10 := call(_9, /** @src 0:151:488  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:466:478  "c.retrieve()" */ _7, sub(/** @src 0:151:488  "contract CallerContract {..." */ _8, /** @src 0:466:478  "c.retrieve()" */ _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                /// @src 0:457:478  "number = c.retrieve()"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:457:478  "number = c.retrieve()" */ expr)
            }
        }
        data ".metadata" hex"a26469706673582212205a3789c805189821227f43912a5ea5141cb30628cec3c7488d840ad92222a35964736f6c634300081e0033"
    }
}

Optimized IR:


```
`EvmYul/Yul/YulSemanticsTests/Caller2.sol`:

```sol
pragma solidity ^0.8.30;

interface StorageContract {
    function store(uint256 num) external;
    function retrieve() external returns (uint256);
}

contract CallerContract {

    uint256 number;

    function testStoreAndRetrieveExternal(uint256 v) public {
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        StorageContract c = StorageContract(storageContractAddr);
        c.store(v);
        number = c.retrieve();
    }

    function testStaticRetrieve() public returns (uint256) {
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        (bool success, bytes memory data) = storageContractAddr.staticcall(
            abi.encodeWithSignature("retrieve()")
        );
        number = abi.decode(data, (uint256));
    }

    function testStaticStore(uint256 value) public returns (uint256) { // Should raise a .StaticModeViolation
        address storageContractAddr = address(0x02); // Ensure StorageContract is set up at address 2
        (bool success, bytes memory data) = storageContractAddr.staticcall(
            abi.encodeWithSignature("store(uint256)", value)
        );
        number = abi.decode(data, (uint256));
    }


}
```
`EvmYul/Yul/YulSemanticsTests/Caller2.yul`:

```yul
Optimized IR:
/// @use-src 0:"Caller2.sol"
object "CallerContract_120" {
    code {
        {
            /// @src 0:151:1255  "contract CallerContract {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("CallerContract_120_deployed")
            codecopy(_1, dataoffset("CallerContract_120_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Caller2.sol"
    object "CallerContract_120_deployed" {
        code {
            {
                /// @src 0:151:1255  "contract CallerContract {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x37cbaee8 {
                        external_fun_testStaticStore()
                    }
                    case 0x5ec1cee6 {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                    case 0x8b1218f9 {
                        external_fun_testStaticRetrieve()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function external_fun_testStaticStore()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_testStaticStore(_1)
                let memPos := mload(64)
                let _2 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_2, memPos))
            }
            function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function external_fun_testStaticRetrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_testStaticRetrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            /// @ast-id 119 @src 0:844:1251  "function testStaticStore(uint256 value) public returns (uint256) { // Should raise a .StaticModeViolation..."
            function fun_testStaticStore(var_value) -> var
            {
                /// @src 0:900:907  "uint256"
                var := /** @src 0:151:1255  "contract CallerContract {..." */ 0
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                let expr_105_mpos := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                let _1 := 0x20
                let _2 := add(expr_105_mpos, _1)
                mstore(_2, shl(224, 0x6057361d))
                _2 := add(expr_105_mpos, 36)
                let _3 := abi_encode_uint256(_2, var_value)
                mstore(expr_105_mpos, add(sub(_3, expr_105_mpos), /** @src 0:151:1255  "contract CallerContract {..." */ not(31)))
                /// @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)"
                finalize_allocation(expr_105_mpos, sub(_3, expr_105_mpos))
                /// @src 0:1096:1198  "storageContractAddr.staticcall(..."
                let _4 := mload(expr_105_mpos)
                let _5 := gas()
                pop(staticcall(_5, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:1096:1198  "storageContractAddr.staticcall(..." */ add(expr_105_mpos, _1), _4, 0, 0))
                let expr_106_component_2_mpos := extract_returndata()
                /// @src 0:151:1255  "contract CallerContract {..."
                let _6 := mload(/** @src 0:1217:1244  "abi.decode(data, (uint256))" */ expr_106_component_2_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_106_component_2_mpos, _1), add(add(expr_106_component_2_mpos, /** @src 0:151:1255  "contract CallerContract {..." */ _6), /** @src 0:1217:1244  "abi.decode(data, (uint256))" */ _1))
                /// @src 0:1208:1244  "number = abi.decode(data, (uint256))"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:1096:1198  "storageContractAddr.staticcall(..." */ 0, /** @src 0:1208:1244  "number = abi.decode(data, (uint256))" */ expr)
            }
            /// @src 0:151:1255  "contract CallerContract {..."
            function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            /// @ast-id 46 @src 0:203:485  "function testStoreAndRetrieveExternal(uint256 v) public {..."
            function fun_testStoreAndRetrieveExternal(var_v)
            {
                /// @src 0:437:447  "c.store(v)"
                let _1 := extcodesize(/** @src 0:151:1255  "contract CallerContract {..." */ 2)
                /// @src 0:437:447  "c.store(v)"
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:437:447  "c.store(v)"
                mstore(_2, /** @src 0:1140:1188  "abi.encodeWithSignature(\"store(uint256)\", value)" */ shl(224, 0x6057361d))
                /// @src 0:437:447  "c.store(v)"
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                /// @src 0:466:478  "c.retrieve()"
                let _7 := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:466:478  "c.retrieve()"
                mstore(_7, /** @src 0:151:1255  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:466:478  "c.retrieve()"
                let _8 := add(_7, /** @src 0:437:447  "c.store(v)" */ 4)
                /// @src 0:466:478  "c.retrieve()"
                let _9 := gas()
                let _10 := call(_9, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:466:478  "c.retrieve()" */ _7, sub(/** @src 0:151:1255  "contract CallerContract {..." */ _8, /** @src 0:466:478  "c.retrieve()" */ _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                /// @src 0:457:478  "number = c.retrieve()"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:437:447  "c.store(v)" */ 0, /** @src 0:457:478  "number = c.retrieve()" */ expr)
            }
            /// @ast-id 81 @src 0:491:838  "function testStaticRetrieve() public returns (uint256) {..."
            function fun_testStaticRetrieve() -> var_
            {
                /// @src 0:537:544  "uint256"
                var_ := /** @src 0:151:1255  "contract CallerContract {..." */ 0
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                let expr_mpos := /** @src 0:151:1255  "contract CallerContract {..." */ mload(64)
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                let _1 := 0x20
                let _2 := add(expr_mpos, _1)
                mstore(_2, /** @src 0:151:1255  "contract CallerContract {..." */ shl(224, 0x2e64cec1))
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                _2 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_2, expr_mpos), /** @src 0:151:1255  "contract CallerContract {..." */ not(31)))
                /// @src 0:738:775  "abi.encodeWithSignature(\"retrieve()\")"
                finalize_allocation(expr_mpos, sub(_2, expr_mpos))
                /// @src 0:694:785  "storageContractAddr.staticcall(..."
                let _3 := mload(expr_mpos)
                let _4 := gas()
                pop(staticcall(_4, /** @src 0:151:1255  "contract CallerContract {..." */ 2, /** @src 0:694:785  "storageContractAddr.staticcall(..." */ add(expr_mpos, _1), _3, 0, 0))
                let expr_component_mpos := extract_returndata()
                /// @src 0:151:1255  "contract CallerContract {..."
                let _5 := mload(/** @src 0:804:831  "abi.decode(data, (uint256))" */ expr_component_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_component_mpos, _1), add(add(expr_component_mpos, /** @src 0:151:1255  "contract CallerContract {..." */ _5), /** @src 0:804:831  "abi.decode(data, (uint256))" */ _1))
                /// @src 0:795:831  "number = abi.decode(data, (uint256))"
                update_storage_value_offset_uint256_to_uint256(/** @src 0:694:785  "storageContractAddr.staticcall(..." */ 0, /** @src 0:795:831  "number = abi.decode(data, (uint256))" */ expr)
            }
        }
        data ".metadata" hex"a2646970667358221220e24661e83e0bb60c2412c749f45703a27bf49c055bcde51c906f337d26b3685564736f6c634300081e0033"
    }
}

Optimized IR:


```
`EvmYul/Yul/YulSemanticsTests/Main.lean`:

```lean
import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

namespace EvmYul

namespace Yul

open Ast SizeLemmas

def callerAddressUInt256 : UInt256 := ⟨1⟩
def storageAddressUInt256 : UInt256 := ⟨2⟩
def caller2AddressUInt256 : UInt256 := ⟨3⟩
def storage2AddressUInt256 : UInt256 := ⟨4⟩
def callerAddress := AccountAddress.ofUInt256 callerAddressUInt256
def storageAddress := AccountAddress.ofUInt256 storageAddressUInt256
def caller2Address := AccountAddress.ofUInt256 caller2AddressUInt256
def storage2Address := AccountAddress.ofUInt256 storage2AddressUInt256


def stateEg₁ : Yul.State :=
  let storageCode : YulContract := 
  
  
{
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x2e64cec1 { external_fun_retrieve() }
                    case 0x6057361d { external_fun_store() }
                    case 0xd54d0506 {
                        external_fun_storageCallCodeTest()
                    }
                    case 0xdd15ce8e {
                        external_fun_storageDelegateCallTest()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "external_fun_retrieve"
          <f
          function external_fun_retrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_retrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "external_fun_store"
          <f
          function external_fun_store()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_store(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "external_fun_storageCallCodeTest"
          <f
          function external_fun_storageCallCodeTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageCallCodeTest()
                return(0, 0)
            }
            
           >

          |>.insert
          "external_fun_storageDelegateCallTest"
          <f
          function external_fun_storageDelegateCallTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageDelegateCallTest()
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "fun_retrieve"
          <f
          function fun_retrieve() -> var
            {
                var :=  sload( 0x00)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_store"
          <f
          function fun_store(var_num)
            {
                update_storage_value_offset_uint256_to_uint256(0x00, var_num)
            }
            
           >

          |>.insert
          "panic_error_0x41"
          <f
          function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            
           >

          |>.insert
          "finalize_allocation"
          <f
          function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            
           >

          |>.insert
          "allocate_memory"
          <f
          function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            
           >

          |>.insert
          "array_allocation_size_bytes"
          <f
          function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            
           >

          |>.insert
          "allocate_memory_array_bytes"
          <f
          function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            
           >

          |>.insert
          "extract_returndata"
          <f
          function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            
           >

          |>.insert
          "fun_storageCallCodeTest"
          <f
          function fun_storageCallCodeTest()
            {
                let expr_mpos :=  mload(64)
                let _1 := add(expr_mpos, 0x20)
                mstore(_1, shl(224, 0x2a24ab1f))
                _1 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_1, expr_mpos),  not(31)))
                finalize_allocation(expr_mpos, sub(_1, expr_mpos))
                let _2 := mload(expr_mpos)
                let _3 := gas()
                pop(callcode(_3,  4, 0, add(expr_mpos,  0x20),  _2, 0, 0))
                pop(extract_returndata())
            }
            
           >

          |>.insert
          "fun_storageDelegateCallTest"
          <f
          function fun_storageDelegateCallTest()
            {
                let expr_55_mpos :=  mload(64)
                let _1 := add(expr_55_mpos, 0x20)
                mstore(_1,  shl(224, 0x2a24ab1f))
                _1 := add(expr_55_mpos, 36)
                mstore(expr_55_mpos, add(sub(_1, expr_55_mpos),  not(31)))
                finalize_allocation(expr_55_mpos, sub(_1, expr_55_mpos))
                let _2 := mload(expr_55_mpos)
                let _3 := gas()
                pop(delegatecall(_3,  4,  add(expr_55_mpos,  0x20),  _2, 0, 0))
                pop(extract_returndata())
            }
        
           >


}  
  
  let storageAccount : Account .Yul :=
    { code := storageCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := Batteries.RBMap.ofList [(⟨0⟩, ⟨21⟩)] compare
    , tstorage := ∅
    }
  let callerCode : YulContract := 
  
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x5ec1cee6, shr(224, calldataload(0)))
                    {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "external_fun_testStoreAndRetrieveExternal"
          <f
          function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20"
          <f
          function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            
           >

          |>.insert
          "panic_error_0x41"
          <f
          function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            
           >

          |>.insert
          "finalize_allocation"
          <f
          function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            
           >

          |>.insert
          "abi_decode_fromMemory"
          <f
          function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "revert_forward"
          <f
          function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            
           >

          |>.insert
          "abi_decode_t_uint256_fromMemory"
          <f
          function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_uint256_fromMemory"
          <f
          function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_testStoreAndRetrieveExternal"
          <f
          function fun_testStoreAndRetrieveExternal(var_v)
            {
                let _1 := 1
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 :=  mload(64)
                mstore(_2,  shl(224, 0x6057361d))
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4,  2,  0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                let _7 :=  mload(64)
                mstore(_7,  shl(224, 0x2e64cec1))
                let _8 := add(_7,  4)
                let _9 := gas()
                let _10 := call(_9,  2,  0,  _7, sub( _8,  _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
        
           >


}
  
  
  let callerAccount : Account .Yul :=
    { code := callerCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
    
    let caller2Code : YulContract := 
    
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x37cbaee8 {
                        external_fun_testStaticStore()
                    }
                    case 0x5ec1cee6 {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                    case 0x8b1218f9 {
                        external_fun_testStaticRetrieve()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "external_fun_testStaticStore"
          <f
          function external_fun_testStaticStore()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                let ret := fun_testStaticStore(_1)
                let memPos := mload(64)
                let _2 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_2, memPos))
            }
            
           >

          |>.insert
          "external_fun_testStoreAndRetrieveExternal"
          <f
          function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "external_fun_testStaticRetrieve"
          <f
          function external_fun_testStaticRetrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_testStaticRetrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "panic_error_0x41"
          <f
          function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            
           >

          |>.insert
          "finalize_allocation"
          <f
          function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            
           >

          |>.insert
          "allocate_memory"
          <f
          function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            
           >

          |>.insert
          "array_allocation_size_bytes"
          <f
          function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            
           >

          |>.insert
          "allocate_memory_array_bytes"
          <f
          function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            
           >

          |>.insert
          "extract_returndata"
          <f
          function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            
           >

          |>.insert
          "abi_decode_t_uint256_fromMemory"
          <f
          function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_uint256_fromMemory"
          <f
          function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_testStaticStore"
          <f
          function fun_testStaticStore(var_value) -> var
            {
                var :=  0
                let expr_105_mpos :=  mload(64)
                let _1 := 0x20
                let _2 := add(expr_105_mpos, _1)
                mstore(_2, shl(224, 0x6057361d))
                _2 := add(expr_105_mpos, 36)
                let _3 := abi_encode_uint256(_2, var_value)
                mstore(expr_105_mpos, add(sub(_3, expr_105_mpos),  not(31)))
                finalize_allocation(expr_105_mpos, sub(_3, expr_105_mpos))
                let _4 := mload(expr_105_mpos)
                let _5 := gas()
                pop(staticcall(_5,  2,  add(expr_105_mpos, _1), _4, 0, 0))
                let expr_106_component_2_mpos := extract_returndata()
                let _6 := mload( expr_106_component_2_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_106_component_2_mpos, _1), add(add(expr_106_component_2_mpos,  _6),  _1))
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
            
           >

          |>.insert
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20"
          <f
          function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode_fromMemory"
          <f
          function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "revert_forward"
          <f
          function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            
           >

          |>.insert
          "fun_testStoreAndRetrieveExternal"
          <f
          function fun_testStoreAndRetrieveExternal(var_v)
            {
                let _1 := extcodesize( 2)
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 :=  mload(64)
                mstore(_2,  shl(224, 0x6057361d))
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4,  2,  0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                let _7 :=  mload(64)
                mstore(_7,  shl(224, 0x2e64cec1))
                let _8 := add(_7,  4)
                let _9 := gas()
                let _10 := call(_9,  2,  0,  _7, sub( _8,  _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
            
           >

          |>.insert
          "fun_testStaticRetrieve"
          <f
          function fun_testStaticRetrieve() -> var_
            {
                var_ :=  0
                let expr_mpos :=  mload(64)
                let _1 := 0x20
                let _2 := add(expr_mpos, _1)
                mstore(_2,  shl(224, 0x2e64cec1))
                _2 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_2, expr_mpos),  not(31)))
                finalize_allocation(expr_mpos, sub(_2, expr_mpos))
                let _3 := mload(expr_mpos)
                let _4 := gas()
                pop(staticcall(_4,  2,  add(expr_mpos, _1), _3, 0, 0))
                let expr_component_mpos := extract_returndata()
                let _5 := mload( expr_component_mpos)
                let expr := abi_decode_uint256_fromMemory(add(expr_component_mpos, _1), add(add(expr_component_mpos,  _5),  _1))
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
        
           >


}
    
    let caller2Account : Account .Yul :=
    { code := caller2Code
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
 
 let storage2Code : YulContract := 
 
 {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x2a24ab1f, shr(224, calldataload(0))) { external_fun_store5() }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "external_fun_store5"
          <f
          function external_fun_store5()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_store5()
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_store5"
          <f
          function fun_store5()
            {
                update_storage_value_offset_uint256_to_uint256(0x00,  0x05)
            }
        
           >


}

let storage2Account : Account .Yul :=
    { code := storage2Code
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
    
  let accountMap : AccountMap .Yul := Batteries.RBMap.insert ∅ storageAddress storageAccount
                                      |>.insert callerAddress callerAccount
                                      |>.insert caller2Address caller2Account
                                      |>.insert storage2Address storage2Account
  let sharedState : SharedState .Yul :=
    { accountMap := accountMap
    , σ₀ := ∅
    , totalGasUsedInBlock := 0
    , transactionReceipts := #[]
    , substate := Inhabited.default
    , executionEnv := 
        { calldata := ByteArray.mk #[]
        , code := Inhabited.default
        , codeOwner := callerAddress
        , source := Inhabited.default
        , weiValue := ⟨0⟩
        , sender := Inhabited.default
        , gasPrice := 0
        , header := (Inhabited.default : BlockHeader)
        , depth := 0
        , perm := true
        , blobVersionedHashes := []
        }
    , blocks := ∅
    , genesisBlockHeader := Inhabited.default
    , createdAccounts := ∅
    , gasAvailable := ⟨0⟩
    , activeWords := ⟨0⟩
    , memory := ByteArray.mk #[]
    , returnData := ByteArray.mk #[]
    , H_return := ByteArray.mk #[]
    }
  Yul.State.Ok sharedState ∅
    
def test₁ :=
  let expr : Expr := .Call (Sum.inr "fun_testStoreAndRetrieveExternal") [.Lit ⟨42⟩]
  match (exec 99 (.ExprStmtCall expr) .none stateEg₁) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def stateEg₂ : Yul.State :=
  Yul.State.Ok {stateEg₁.toSharedState with executionEnv := {stateEg₁.toSharedState.executionEnv with codeOwner := caller2Address, perm := true}} Inhabited.default
  
def test₂ :=
  let expr : Expr := .Call (Sum.inr "fun_testStaticRetrieve") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₂) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def test₃ :=
  let expr : Expr := .Call (Sum.inr "fun_testStaticStore") [.Lit ⟨42⟩]
  match (exec 99 (.ExprStmtCall expr) .none stateEg₂) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def stateEg₄ : Yul.State :=
  Yul.State.Ok {stateEg₁.toSharedState with executionEnv := {stateEg₁.toSharedState.executionEnv with codeOwner := storageAddress, perm := true}} Inhabited.default


def test₄ :=
  let expr : Expr := .Call (Sum.inr "fun_storageDelegateCallTest") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₄) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

def test₅ :=
  let expr : Expr := .Call (Sum.inr "fun_storageCallCodeTest") []
  match (exec 99 (.ExprStmtCall expr) .none stateEg₄) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"


end Yul

end EvmYul

open EvmYul.Yul

-- Run this test via `lake exe yulSemanticsTests`.
-- `#eval` cannot run the test because it uses the foreign function interface for `ByteArray.zeroes`.
def main : IO Unit := do
  IO.println (s!"test₁: {test₁} -- " ++ (if s!"{test₁}" = "[1 [(0, 42)], 2 [(0, 42)], 3 [], 4 []]" then "Success" else "Failure"))
  IO.println (s!"test₂: {test₂} -- " ++ (if s!"{test₂}" = "[1 [], 2 [(0, 21)], 3 [(0, 21)], 4 []]" then "Success" else "Failure"))
  IO.println (s!"test₃: {test₃} -- " ++ (if s!"{test₃}" = "StaticModeViolation" then "Success" else "Failure"))
  IO.println (s!"test₄: {test₄} -- " ++ (if s!"{test₄}" = "[1 [], 2 [(0, 5)], 3 [], 4 []]" then "Success" else "Failure"))
  IO.println (s!"test₅: {test₅} -- " ++ (if s!"{test₅}" = "[1 [], 2 [(0, 5)], 3 [], 4 []]" then "Success" else "Failure"))

```
`EvmYul/Yul/YulSemanticsTests/README.md`:

```md
# Testing the Yul semantics

To test the Yul semantics with a custom Solidity smart contract, follow these guidelines.

1.

Compile the contracts to test into Yul such as with:

```
SOLC_VERSION=0.8.30 solc --optimize --ir-optimized --yul-optimizations 'ho[esj]x[esVur]' Storage.sol > Storage.yul
```

`solc-select` can be obtained via running `nix-shell` in this directory (to get Nix see https://nixos.org).

2. Follow the example of `Main.lean` and put the dispatcher (which is the Yul code between the braces without a function name, after, e.g. `object "Storage_25_deployed"`) into the body of `dispatcher := ...` inside a definition of type `YulContract`. Enclose the Yul code inside the syntax `<s ... >`. Remove comments and `memoryguard(...)` (keep the argument of `memoryguard`).

3. Follow the example of `Main.lean` and add each named function in the `FinMap` of `functions := ...` where the key of the `FinMap` is a string of the name of the function (with no arguments). Enclose the Yul function (including it's name and arguments) inside the syntax `<f ... >`. Remove comments and `memoryguard(...)` (keep the argument of `memoryguard`).

4. Set up a call, such as in the example of `test₁` in `Main.lean`. Note that the `codeOwner` in the state needs to be set appropriately, such as to the address, `callerAddress` of the smart contract as it has been defined in the state.

5. Due to dependencies on foreign functions, we need to use `lake exe yulSemanticsTests` to run the tests (rather than `#eval`). If necessary modify `lakefile.lean` to run your `.lean` file, see the example of `lean_exe «yulSemanticsTests»`.
```
`EvmYul/Yul/YulSemanticsTests/Storage.sol`:

```sol
pragma solidity >=0.8.2 <0.9.0;

interface Storage2Contract {
    function store5() external;
}

contract Storage {

    uint256 number;

    function store(uint256 num) public {
        number = num;
    }

    function retrieve() public view returns (uint256){
        return number;
    }

    function storageDelegateCallTest() public {
        address storage2ContractAddr = address(0x04); // Ensure Storage2Contract is set up at address 4
        Storage2Contract c = Storage2Contract(storage2ContractAddr);
        (bool success, ) = address(c).delegatecall(
            abi.encodeWithSignature("store5()")
        );       
    }

    function storageCallCodeTest() public {
        address storage2ContractAddr = address(0x04); // Ensure Storage2Contract is set up at address 4
        Storage2Contract c = Storage2Contract(storage2ContractAddr);
        (bool success, ) = address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)
            abi.encodeWithSignature("store5()")
        );       
    }

    
}
```
`EvmYul/Yul/YulSemanticsTests/Storage.yul`:

```yul
Optimized IR:
/// @use-src 0:"Storage.sol"
object "Storage_88" {
    code {
        {
            /// @src 0:97:1065  "contract Storage {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("Storage_88_deployed")
            codecopy(_1, dataoffset("Storage_88_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Storage.sol"
    object "Storage_88_deployed" {
        code {
            {
                /// @src 0:97:1065  "contract Storage {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x2e64cec1 { external_fun_retrieve() }
                    case 0x6057361d { external_fun_store() }
                    case 0xd54d0506 {
                        external_fun_storageCallCodeTest()
                    }
                    case 0xdd15ce8e {
                        external_fun_storageDelegateCallTest()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            function external_fun_retrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_retrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            function external_fun_store()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_store(_1)
                return(0, 0)
            }
            function external_fun_storageCallCodeTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageCallCodeTest()
                return(0, 0)
            }
            function external_fun_storageDelegateCallTest()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_storageDelegateCallTest()
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            /// @ast-id 25 @src 0:212:291  "function retrieve() public view returns (uint256){..."
            function fun_retrieve() -> var
            {
                /// @src 0:271:284  "return number"
                var := /** @src 0:97:1065  "contract Storage {..." */ sload(/** @src 0:278:284  "number" */ 0x00)
            }
            /// @src 0:97:1065  "contract Storage {..."
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            /// @ast-id 17 @src 0:142:206  "function store(uint256 num) public {..."
            function fun_store(var_num)
            {
                /// @src 0:187:199  "number = num"
                update_storage_value_offset_uint256_to_uint256(0x00, var_num)
            }
            /// @src 0:97:1065  "contract Storage {..."
            function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            function allocate_memory(size) -> memPtr
            {
                memPtr := mload(64)
                finalize_allocation(memPtr, size)
            }
            function array_allocation_size_bytes(length) -> size
            {
                if gt(length, 0xffffffffffffffff) { panic_error_0x41() }
                size := and(add(length, 31), not(31))
                size := add(size, 0x20)
            }
            function allocate_memory_array_bytes(length) -> memPtr
            {
                let _1 := array_allocation_size_bytes(length)
                memPtr := allocate_memory(_1)
                mstore(memPtr, length)
            }
            function extract_returndata() -> data
            {
                let _1 := returndatasize()
                switch _1
                case 0 { data := 96 }
                default {
                    let _2 := returndatasize()
                    data := allocate_memory_array_bytes(_2)
                    let _3 := returndatasize()
                    returndatacopy(add(data, 0x20), 0, _3)
                }
            }
            /// @ast-id 87 @src 0:643:1057  "function storageCallCodeTest() public {..."
            function fun_storageCallCodeTest()
            {
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                let expr_mpos := /** @src 0:97:1065  "contract Storage {..." */ mload(64)
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                let _1 := add(expr_mpos, 0x20)
                mstore(_1, shl(224, 0x2a24ab1f))
                _1 := add(expr_mpos, 36)
                mstore(expr_mpos, add(sub(_1, expr_mpos), /** @src 0:97:1065  "contract Storage {..." */ not(31)))
                /// @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")"
                finalize_allocation(expr_mpos, sub(_1, expr_mpos))
                /// @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..."
                let _2 := mload(expr_mpos)
                let _3 := gas()
                pop(delegatecall(_3, /** @src 0:97:1065  "contract Storage {..." */ 4, /** @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..." */ add(expr_mpos, /** @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")" */ 0x20), /** @src 0:883:1043  "address(c).delegatecall( // Manually change this to callcode in Yul (Solidity has deprecated callcode)..." */ _2, 0, 0))
                pop(extract_returndata())
            }
            /// @ast-id 56 @src 0:297:637  "function storageDelegateCallTest() public {..."
            function fun_storageDelegateCallTest()
            {
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                let expr_52_mpos := /** @src 0:97:1065  "contract Storage {..." */ mload(64)
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                let _1 := add(expr_52_mpos, 0x20)
                mstore(_1, /** @src 0:998:1033  "abi.encodeWithSignature(\"store5()\")" */ shl(224, 0x2a24ab1f))
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                _1 := add(expr_52_mpos, 36)
                mstore(expr_52_mpos, add(sub(_1, expr_52_mpos), /** @src 0:97:1065  "contract Storage {..." */ not(31)))
                /// @src 0:578:613  "abi.encodeWithSignature(\"store5()\")"
                finalize_allocation(expr_52_mpos, sub(_1, expr_52_mpos))
                /// @src 0:541:623  "address(c).delegatecall(..."
                let _2 := mload(expr_52_mpos)
                let _3 := gas()
                pop(delegatecall(_3, /** @src 0:97:1065  "contract Storage {..." */ 4, /** @src 0:541:623  "address(c).delegatecall(..." */ add(expr_52_mpos, /** @src 0:578:613  "abi.encodeWithSignature(\"store5()\")" */ 0x20), /** @src 0:541:623  "address(c).delegatecall(..." */ _2, 0, 0))
                pop(extract_returndata())
            }
        }
        data ".metadata" hex"a2646970667358221220960c90ddc77bdca69249506d3086cedee34ff2ced8c968d61928a12d4bb5c0d164736f6c634300081e0033"
    }
}

Optimized IR:


```
`EvmYul/Yul/YulSemanticsTests/Storage2.sol`:

```sol
pragma solidity ^0.8.30;

contract Storage {

    uint256 number;

    // Intended for testing DELEGATECALL
    function store5() public {
        number = 5;
    }
}
```
`EvmYul/Yul/YulSemanticsTests/Storage2.yul`:

```yul
Optimized IR:
/// @use-src 0:"Storage2.sol"
object "Storage_12" {
    code {
        {
            /// @src 0:26:166  "contract Storage {..."
            mstore(64, memoryguard(0x80))
            if callvalue()
            {
                revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            }
            let _1 := mload(64)
            let _2 := datasize("Storage_12_deployed")
            codecopy(_1, dataoffset("Storage_12_deployed"), _2)
            return(_1, _2)
        }
        function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
        { revert(0, 0) }
    }
    /// @use-src 0:"Storage2.sol"
    object "Storage_12_deployed" {
        code {
            {
                /// @src 0:26:166  "contract Storage {..."
                mstore(64, memoryguard(0x80))
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x2a24ab1f, shr(224, calldataload(0))) { external_fun_store5() }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            }
            function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            function external_fun_store5()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                fun_store5()
                return(0, 0)
            }
            function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            /// @ast-id 11 @src 0:112:164  "function store5() public {..."
            function fun_store5()
            {
                /// @src 0:147:157  "number = 5"
                update_storage_value_offset_uint256_to_uint256(0x00, /** @src 0:156:157  "5" */ 0x05)
            }
        }
        data ".metadata" hex"a264697066735822122063cdb8d37932ac731b01dc445558cd9551bf6e082a61c08a0b1561eed01c96d964736f6c634300081e0033"
    }
}


```
`EvmYul/Yul/YulSemanticsTests/shell.nix`:

```nix
let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-24.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShell {
  packages = with pkgs; [
    solc-select
  ];
}

```
`README.md`:

```md
This repository contains a formal model of the EVM and Yul in Lean 4.
Where applicable, the underlying EVM primops are used directly by the Yul model.

Everything here is work in progress and is subject to change therefore.

# Requirements
- Python packages: coincurve, typing-extensions, pycryptodome, eth-typing, py-ecc

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
EvmYul/Operations.lean
```

The semantic function `primCall` associated with the ADT:
```
EvmYul/Yul/PrimOps.lean
```

## EVM
The model of the EVM state `EVM.State`:
```
EvmYul/EVM/State.lean
```

The semantic function `step`:
```
EvmYul/EVM/Semantics.lean
```

## Yul
The ADT `Stmt` mutually defined with `Expr` and `FunctionDefinition` describing Yul:
```
EvmYul/Yul/Ast.lean
```

The model of the Yul state `YUL.State`:
```
EvmYul/Yul/State.lean
```

The semantic function `exec` mutually defined with `eval` (and some misc. functions):
```
EvmYul/Yul/Interpreter.lean
```

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.

# Yul semantics tests

To execute the Yul semantics tests run:

`lake exe yulSemanticsTests`

These tests are defined in `EvmYul/Yul/YulSemanticsTests/Main.lean`.

# Limitations of the Yul semantics

## Fallback function from receiving ether

- We do not run a the fallback function of a smart contract when it receives ether, such as being a recipient of ether in a `SELFDESTRUCT` of another contract.

## Gas

- We do not model gas in the Yul semantics, no fee is deducted.

## Create

- We do not model `create` or `create2` because Yul code is not stored as bytecode, and so we cannot properly model `create` or `create2` without some mechanism for correctly decompiling bytecode into Yul code, so we do not model this.
- This case is caught by the the `_` in the match statement in `EVMYul/Semantics.lean` and returns `default`.
- Instead of creating contracts, they should be manually included in the modelled blockchain state, in the `accountMap`. See `EvmYul/Yul/YulSemanticsTests/README.md` for more information on how to include custom Solidity contracts in the modelled blockchain state.

## EXTCODESIZE

- Not modelled, the current semantics raise an error. Solidity checks `extcodesize` and so generated Yul will not be able to call other contracts without removing or editing these `extcodesize` checks (manually).
- In the `EvmYul/Yul/YulSemanticsTests.lean` we manually changed `let _1 := extcodesize( 2)` to `let _1 := 1` in `fun_testStoreAndRetrieveExternal`.

## Other contract code related opcodes not modelled
- We also do not model `EXTCODEHASH`, `EXTCODECOPY`, `CODECOPY`, `CODESIZE` for similar reasons to not modelling `EXTCODESIZE`.
- These cases are caught by the the `_` in the match statement in `EVMYul/Semantics.lean` and return `default`.

## SELFDESTRUCT

- Halting for `SELFDESTRUCT` is not implemented and the semantics for `SELFDESTRUCT` have limitations, such as not triggering the fallback function in a contract that is the recipient of the ether from the contract the self-destructs. We may remove the semantics for `SELFDESTRUCT` once its status changes from deprecated to not being supported.
```
`SpongeHash.lean`:

```lean
-- This module serves as the root of the `SpongeHash` library.
-- Import modules here that should be built as part of the library.
import «SpongeHash».Basic
import «SpongeHash».Keccak256

```
`lake-manifest.json`:

```json
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover-community/mathlib4.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "79e94a093aff4a60fb1b1f92d9681e407124c2ca",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "b100ad4c5d74a464f497aaa8e7c74d86bf39a56f",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "99657ad92e23804e279f77ea6dbdeebaa1317b98",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "eb164a46de87078f27640ee71e6c3841defc2484",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "1253a071e6939b0faf5c09d2b30b0bfc79dae407",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.68",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "1256a18522728c2eeed6109b02dd2b8f207a2a3c",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "917bfa5064b812b7fbd7112d018ea0b4def25ab3",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "240676e9568c254a69be94801889d4b13f3b249f",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.22.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "leanprover",
   "rev": "c682c91d2d4dd59a7187e2ab977ac25bd1f87329",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "evmyul",
 "lakeDir": ".lake"}

```
`lakefile.lean`:

```lean
import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.22.0"

package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

def cloneWithCache (pkg : NPackage _package.name) (dirname url : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  if !(←System.FilePath.pathExists "EthereumTests") then
    dbg_trace s!"Cloning EthereumTests into a submodule."
    discard <| IO.Process.run {cmd := "git", args := #["submodule", "update", "--init"]}

  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[sha256O, keccak256, ffiO]

lean_lib «Conform»

@[default_target]
lean_lib «EvmYul»

@[test_driver]
lean_exe «conform» where
  root := `Conform.Main

lean_exe «yulSemanticsTests» where
  root := `EvmYul.Yul.YulSemanticsTests.Main

```
`lean-toolchain`:

```
leanprover/lean4:v4.22.0

```
`license.txt`:

```txt
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2024 Demerzel Solutions Limited (t/a Nethermind)

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

```
`openssl.cnf`:

```cnf
openssl_conf = openssl_init

[openssl_init]
providers = provider_sect

[provider_sect]
default = default_sect
legacy = legacy_sect

[default_sect]
activate = 1

[legacy_sect]
activate = 1

```
`shell.nix`:

```nix
let
  nixpkgs = fetchTarball "https://github.com/NixOS/nixpkgs/tarball/nixos-24.11";
  pkgs = import nixpkgs { config = {}; overlays = []; };
in

pkgs.mkShell {
  packages = with pkgs; [
    elan
    python312Packages.coincurve
    python312Packages.typing-extensions
    python312Packages.pycryptodome
    python312Packages.eth-typing
    python312Packages.py-ecc
    pkgs.openssl
  ];
  shellHook = ''
    export LD_LIBRARY_PATH=${pkgs.openssl.out}/lib:$LD_LIBRARY_PATH
  '';
}

```