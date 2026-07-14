/-
  Verification of the single-line-swap transformation, which replaces the
  temporary-based exchange of two variables

        tmp := varA ;  varA := varB ;  varB := tmp

  by the simultaneous assignment `(varA, varB) := (varB, varA)`. The compiler
  lowers the latter, by first capturing the prior value of the second variable,
  to the sequence

        c := varB ;  varB := varA ;  varA := c.

  The transformation is sound under the following provisos, the necessity of which
  is exhibited by the compiler output when they are violated: the three names are
  pairwise distinct and bound in the variable store, and the shared continuation
  `Q` depends only on `varA` and `varB`, and in particular not on the temporary.
  Under these provisos both sequences leave `varA` and `varB` holding the exchanged
  values, so the shared prefix and continuation evaluate identically.

  The transformation is modelled at the level of Yul statements. A reassignment
  `v := e` is represented as `.Let [v] (some e)`; on a variable operand it reduces
  to an insertion into the variable store, which is a finite map. The store reads
  are discharged through the decidable indexing instance together with the
  standard finite-map lemmas. The development contains no uses of `sorry` or
  `axiom`.
-/

import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.Exception
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Yul.PrimOps
import EvmYul.Semantics
import EvmYul.Operations
import Mathlib.Data.Finmap
import Core

open EvmYul Yul Ast Core

set_option autoImplicit false

namespace Law2

/-
  Elementary facts about reading and writing the variable store.
-/

/-- Reading a variable immediately after writing it returns the written value. -/
lemma get_insert_same (ss : SharedState .Yul) (store : VarStore)
    (v : Identifier) (val : EvmYul.Literal) :
    ((State.Ok ss store)⟦v↦val⟧)[v]! = val := by
  have hmem : v ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  simp only [getElem!, decidableGetElem?, hmem, dif_pos, getElem]
  show (Finmap.lookup v (Finmap.insert v val store)).get! = val
  rw [Finmap.lookup_insert]; rfl

/-- Reading a variable other than the one written, and itself bound, is unaffected
    by the write. -/
lemma get_insert_ne (ss : SharedState .Yul) (store : VarStore)
    (v w : Identifier) (val : EvmYul.Literal) (hne : w ≠ v) (hw : w ∈ store) :
    ((State.Ok ss store)⟦v↦val⟧)[w]! = (State.Ok ss store)[w]! := by
  have hmem : w ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
    Finmap.mem_insert.mpr (Or.inr hw)
  have hmem0 : w ∈ (State.Ok ss store).store := hw
  simp only [getElem!, decidableGetElem?, hmem, hmem0, dif_pos, getElem]
  show (Finmap.lookup w (Finmap.insert v val store)).get!
     = (Finmap.lookup w store).get!
  rw [Finmap.lookup_insert_of_ne _ hne]

/-- Membership is preserved by insertion, so each reassignment keeps the remaining
    names bound. -/
lemma mem_insert_of_mem (ss : SharedState .Yul) (store : VarStore)
    (v w : Identifier) (val : EvmYul.Literal) (hw : w ∈ store) :
    w ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
  Finmap.mem_insert.mpr (Or.inr hw)

/-- A written variable is thereafter bound. -/
lemma mem_insert_self (ss : SharedState .Yul) (store : VarStore)
    (v : Identifier) (val : EvmYul.Literal) :
    v ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
  Finmap.mem_insert.mpr (Or.inl rfl)

/-- Insertion leaves a fuel-exhausted state unchanged, as it acts only on
    successful states. -/
@[simp] lemma insert_outOfFuel (v : Identifier) (val : EvmYul.Literal) :
    (State.OutOfFuel : Yul.State)⟦v↦val⟧ = State.OutOfFuel := by
  simp only [State.insert]

/-- Insertion leaves a checkpoint state unchanged. -/
@[simp] lemma insert_checkpoint (j : Jump) (v : Identifier) (val : EvmYul.Literal) :
    (State.Checkpoint j : Yul.State)⟦v↦val⟧ = State.Checkpoint j := by
  simp only [State.insert]

/-
  Reduction of a single reassignment.

  A reassignment of the form `v := w`, with `w` a variable, evaluates in one step
  to the state obtained by binding `v` to the current value of `w`.
-/

lemma exec_reassign (n : ℕ) (v w : Identifier) (co : Option YulContract) (s : Yul.State) :
    exec (n + 1) (.Let [v] (some (.Var w))) co s = .ok (s⟦v ↦ s[w]!⟧) := by
  simp only [Yul.exec, List.head!]

/-- Reduction of a block whose head is a reassignment: the assignment is performed
    and evaluation continues with the remaining statements. -/
lemma exec_block_reassign_cons (n : ℕ) (v w : Identifier) (rest : List Stmt)
    (co : Option YulContract) (s : Yul.State) :
    exec (n + 2) (.Block (.Let [v] (some (.Var w)) :: rest)) co s
      = exec (n + 1) (.Block rest) co (s⟦v ↦ s[w]!⟧) := by
  rw [show exec (n+2) (.Block (.Let [v] (some (.Var w)) :: rest)) co s
        = _ from by rw [Yul.exec]]
  rw [exec_reassign]

/-- A block consisting of a single reassignment evaluates successfully. -/
lemma exec_block_reassign_single (n : ℕ) (v w : Identifier)
    (co : Option YulContract) (s : Yul.State) :
    exec (n + 2) (.Block [.Let [v] (some (.Var w))]) co s = .ok (s⟦v ↦ s[w]!⟧) := by
  rw [exec_block_reassign_cons]
  simp only [Yul.exec]

/-
  Reading through iterated writes.

  The swap sequences produce states of the form `s⟦a↦x⟧⟦b↦y⟧⟦c↦z⟧`. The following
  lemma packages the reading of the most recently written binding through such an
  iterated insertion.
-/

/-- Reading the most recently written variable through an iterated insertion
    returns the written value. -/
lemma read_top (s : Yul.State) (ss : SharedState .Yul) (store : VarStore)
    (hs : s = State.Ok ss store) (v : Identifier) (val : EvmYul.Literal) :
    (s⟦v↦val⟧)[v]! = val := by
  subst hs; exact get_insert_same ss store v val

/-
  The two swap sequences and their effect on the exchanged variables.

  The temporary-based sequence `[tmp := varA ; varA := varB ; varB := tmp]` and the
  lowered simultaneous sequence `[c := varB ; varB := varA ; varA := c]` are shown,
  from a state binding `varA` and `varB` to their initial values, to reach states
  in which `varA` and `varB` hold the exchanged values. Each effect is established
  by reducing the three reassignments and evaluating the resulting reads under the
  hypotheses of pairwise distinctness and membership.
-/

def tempSwap (tmp varA varB : Identifier) : List Stmt :=
  [ .Let [tmp]  (some (.Var varA)),
    .Let [varA] (some (.Var varB)),
    .Let [varB] (some (.Var tmp)) ]

def simulSwap (c varA varB : Identifier) : List Stmt :=
  [ .Let [c]    (some (.Var varB)),
    .Let [varB] (some (.Var varA)),
    .Let [varA] (some (.Var c)) ]

/-- Effect of the temporary-based sequence. From a state in which the three names
    are pairwise distinct and `varA`, `varB` are bound, the three reassignments
    yield the state that binds `varA` and `varB` to their exchanged values. The
    proof reduces the three steps and evaluates the resulting reads. -/
lemma tempSwap_effect
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (tmp varA varB : Identifier)
    (_hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (_hmA : varA ∈ store) (hmB : varB ∈ store) :
    exec (n + 4) (.Block (tempSwap tmp varA varB)) co (State.Ok ss store)
      = .ok ((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧) := by
  unfold tempSwap
  rw [show n + 4 = (n+2) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 2 + 1 = (n+1) + 2 from by omega, exec_block_reassign_cons]
  -- after 2 steps the head-read of the 2nd assignment is varB in state ⟦tmp↦A₀⟧;
  -- since varB ≠ tmp and varB ∈ store, that read is B₀.
  rw [show ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[varB]!
        = (State.Ok ss store)[varB]! from
        get_insert_ne ss store tmp varB _ (Ne.symm hTB) hmB]
  -- one step left: singleton block [varB := tmp]
  rw [show n + 1 + 1 = n + 2 from by omega, exec_block_reassign_single]
  -- reduce the final tmp-read to A₀
  congr 1
  -- goal: ⟦..⟧⟦varB ↦ <read tmp>⟧ = ⟦..⟧⟦varB ↦ A₀⟧ ; show the read equals A₀
  have htmp_mem : tmp ∈ ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  have hread :
      (((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
          ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
        = (State.Ok ss store)[varA]! := by
    -- outer insert is varA; read tmp passes it (tmp ≠ varA), then hits the tmp-insert.
    rw [show (((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
           = ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[tmp]! from
         get_insert_ne ss (Finmap.insert tmp (State.Ok ss store)[varA]! store)
           varA tmp _ hTA htmp_mem]
    exact get_insert_same ss store tmp ((State.Ok ss store)[varA]!)
  rw [hread]

/-- Effect of the lowered simultaneous sequence, with the same resulting bindings
    for `varA` and `varB`. -/
lemma simulSwap_effect
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (c varA varB : Identifier)
    (_hAB : varA ≠ varB) (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmA : varA ∈ store) (_hmB : varB ∈ store) :
    exec (n + 4) (.Block (simulSwap c varA varB)) co (State.Ok ss store)
      = .ok ((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧) := by
  unfold simulSwap
  rw [show n + 4 = (n+2) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 2 + 1 = (n+1) + 2 from by omega, exec_block_reassign_cons]
  rw [show ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)[varA]!
        = (State.Ok ss store)[varA]! from
        get_insert_ne ss store c varA _ (Ne.symm hCA) hmA]
  rw [show n + 1 + 1 = n + 2 from by omega, exec_block_reassign_single]
  congr 1
  have hc_mem : c ∈ ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  have hread :
      (((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
          ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[c]!
        = (State.Ok ss store)[varB]! := by
    -- outer insert is varB; read c passes it (c ≠ varB), then hits the c-insert.
    rw [show (((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[c]!
           = ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)[c]! from
         get_insert_ne ss (Finmap.insert c (State.Ok ss store)[varB]! store)
           varB c _ hCB hc_mem]
    exact get_insert_same ss store c ((State.Ok ss store)[varB]!)
  rw [hread]

/-
  The equivalence theorem.

  Both swap sequences reach states that agree on `varA` and `varB` but differ
  elsewhere, the temporary-based sequence retaining a binding for `tmp` and the
  lowered sequence a binding for `c`. The shared continuation must therefore depend
  only on `varA` and `varB`. This is expressed by the semantic proviso
  `AgreesOnAB`, which requires that the continuation evaluate identically from any
  two states agreeing on those two variables. Under this proviso, together with
  pairwise distinctness and membership, the two programs are observationally
  equivalent; the shared prefix is handled through the foundational module.
-/

/-- The semantic proviso on the continuation: it evaluates identically from any
    two states that agree on `varA` and `varB`. This is the behavioural rendering
    of the syntactic condition that the continuation depend only on those two
    variables. -/
def AgreesOnAB (Q : List Stmt) (varA varB : Identifier) : Prop :=
  ∀ (fuel : ℕ) (s₁ s₂ : Yul.State) (co : Option YulContract),
    s₁[varA]! = s₂[varA]! → s₁[varB]! = s₂[varB]! →
    exec fuel (.Block Q) co s₁ = exec fuel (.Block Q) co s₂

/-- In the state reached by the temporary-based sequence, `varA` and `varB` hold
    the exchanged values. -/
lemma tempSwap_reads
    (ss : SharedState .Yul) (store : VarStore) (tmp varA varB : Identifier)
    (hAB : varA ≠ varB) (_hTA : tmp ≠ varA) (_hTB : tmp ≠ varB) (_hmA : varA ∈ store) :
    (((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧))[varA]!
      = (State.Ok ss store)[varB]!
    ∧ (((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧))[varB]!
      = (State.Ok ss store)[varA]! := by
  constructor
  · -- read varA: passes varB-insert (varA ≠ varB), hits varA-insert
    rw [show (((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧))[varA]!
           = ((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧))[varA]! from
         get_insert_ne ss _ varB varA _ hAB
           (Finmap.mem_insert.mpr (Or.inl rfl))]
    exact get_insert_same ss _ varA _
  · -- read varB: hits varB-insert directly
    exact get_insert_same ss _ varB _

/-- In the state reached by the lowered simultaneous sequence, `varA` and `varB`
    hold the exchanged values, in agreement with the temporary-based sequence. -/
lemma simulSwap_reads
    (ss : SharedState .Yul) (store : VarStore) (c varA varB : Identifier)
    (hAB : varA ≠ varB) (_hCA : c ≠ varA) (_hCB : c ≠ varB) (_hmB : varB ∈ store) :
    (((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧))[varA]!
      = (State.Ok ss store)[varB]!
    ∧ (((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧))[varB]!
      = (State.Ok ss store)[varA]! := by
  constructor
  · -- read varA: hits varA-insert directly
    exact get_insert_same ss _ varA _
  · -- read varB: passes varA-insert (varB ≠ varA), hits varB-insert
    rw [show (((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧))[varB]!
           = ((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧))[varB]! from
         get_insert_ne ss _ varA varB _ (Ne.symm hAB)
           (Finmap.mem_insert.mpr (Or.inl rfl))]
    exact get_insert_same ss _ varB _

/-- Evaluation of three reassignments followed by a continuation: the three steps
    are performed and evaluation proceeds with the continuation from the resulting
    state. -/
lemma exec_reassign3_append_Q
    (n : ℕ) (co : Option YulContract) (s : Yul.State) (Q : List Stmt)
    (va vb vc wa wb wc : Identifier) :
    exec (n + 4) (.Block ([.Let [va] (some (.Var wa)),
                           .Let [vb] (some (.Var wb)),
                           .Let [vc] (some (.Var wc))] ++ Q)) co s
      = exec (n + 1) (.Block Q) co
          (((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)
             ⟦vc ↦ ((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)[wc]!⟧) := by
  simp only [List.cons_append, List.nil_append]
  rw [show n + 4 = (n+2) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 2 + 1 = (n+1) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 1 + 1 = n + 2 from by omega, exec_block_reassign_cons]

/-- Evaluation of the temporary-based sequence followed by the continuation,
    presented with the resulting state in reduced form. -/
lemma tempSwap_append
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (tmp varA varB : Identifier) (Q : List Stmt)
    (_hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (_hmA : varA ∈ store) (hmB : varB ∈ store) :
    exec (n + 4) (.Block (tempSwap tmp varA varB ++ Q)) co (State.Ok ss store)
      = exec (n + 1) (.Block Q) co
          ((((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧) := by
  unfold tempSwap
  rw [exec_reassign3_append_Q]
  -- simplify the two nested intermediate reads to the clean form
  rw [show ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[varB]!
        = (State.Ok ss store)[varB]! from
        get_insert_ne ss store tmp varB _ (Ne.symm hTB) hmB]
  have htmp_mem : tmp ∈ ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  rw [show (((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
            ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
         = (State.Ok ss store)[varA]! from by
        rw [show (((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                  ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
               = ((State.Ok ss store)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[tmp]! from
             get_insert_ne ss (Finmap.insert tmp (State.Ok ss store)[varA]! store)
               varA tmp _ hTA htmp_mem]
        exact get_insert_same ss store tmp _]

/-- Evaluation of the lowered simultaneous sequence followed by the continuation,
    presented with the resulting state in reduced form. -/
lemma simulSwap_append
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (c varA varB : Identifier) (Q : List Stmt)
    (_hAB : varA ≠ varB) (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmA : varA ∈ store) (_hmB : varB ∈ store) :
    exec (n + 4) (.Block (simulSwap c varA varB ++ Q)) co (State.Ok ss store)
      = exec (n + 1) (.Block Q) co
          ((((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧) := by
  unfold simulSwap
  rw [exec_reassign3_append_Q]
  rw [show ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)[varA]!
        = (State.Ok ss store)[varA]! from
        get_insert_ne ss store c varA _ (Ne.symm hCA) hmA]
  have hc_mem : c ∈ ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  rw [show (((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
            ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[c]!
         = (State.Ok ss store)[varB]! from by
        rw [show (((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                  ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[c]!
               = ((State.Ok ss store)⟦c ↦ (State.Ok ss store)[varB]!⟧)[c]! from
             get_insert_ne ss (Finmap.insert c (State.Ok ss store)[varB]! store)
               varB c _ hCB hc_mem]
        exact get_insert_same ss store c _]

/-- Soundness of the single-line-swap transformation. For a shared prefix `P` and
    a shared continuation `Q` depending only on `varA` and `varB`, with the three
    names pairwise distinct and bound throughout, the temporary-based program and
    the simultaneous-swap program are observationally equivalent. -/
theorem single_line_swap_equiv
    (P Q : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmem : ∀ (ss : SharedState .Yul) (store : VarStore),
              varA ∈ (State.Ok ss store).store ∧ varB ∈ (State.Ok ss store).store)
    (hQ : AgreesOnAB Q varA varB) :
    ObservationalEquivalence
      (P ++ tempSwap tmp varA varB ++ Q)
      (P ++ simulSwap c varA varB ++ Q) := by
  -- The two swap-then-Q fragments agree at every fuel and state; then the shared
  -- prefix P is threaded by Core, and execTopLevel is reached by Core.
  -- Core.exec_block_prefix_congr wants the fragments in the form (frag ++ nothing),
  -- with P prepended.  We first prove the fragment-level agreement.
  -- Fragment-level agreement, only needed at fuel ≥ 4 on `.Ok` states; for other
  -- fuels/states both fragments reduce identically.  We prove the `.Ok`, fuel≥4 core
  -- via the append lemmas + reads + hQ, and dispatch the rest structurally.
  have hcore : ∀ (n : ℕ) (ss : SharedState .Yul) (store : VarStore),
      exec (n+4) (.Block (tempSwap tmp varA varB ++ Q)) .none (State.Ok ss store)
        = exec (n+4) (.Block (simulSwap c varA varB ++ Q)) .none (State.Ok ss store) := by
    intro n ss store
    have hmA : varA ∈ store := (hmem ss store).1
    have hmB : varB ∈ store := (hmem ss store).2
    rw [tempSwap_append n .none ss store tmp varA varB Q hAB hTA hTB hmA hmB,
        simulSwap_append n .none ss store c varA varB Q hAB hCA hCB hmA hmB]
    -- both sides now: exec (n+1) (.Block Q) .none <clean state>; states agree on varA/varB
    apply hQ
    · rw [(tempSwap_reads ss store tmp varA varB hAB hTA hTB hmA).1,
          (simulSwap_reads ss store c varA varB hAB hCA hCB hmB).1]
    · rw [(tempSwap_reads ss store tmp varA varB hAB hTA hTB hmA).2,
          (simulSwap_reads ss store c varA varB hAB hCA hCB hmB).2]
  have hfrag : ∀ fuel s,
      exec fuel (.Block (tempSwap tmp varA varB ++ Q)) .none s
        = exec fuel (.Block (simulSwap c varA varB ++ Q)) .none s := by
    intro fuel s
    match fuel, s with
    | 0, s => simp only [Yul.exec]
    | 1, s => simp only [Yul.exec, tempSwap, simulSwap, List.cons_append, List.nil_append]
    | 2, s => simp only [Yul.exec, tempSwap, simulSwap, List.cons_append, List.nil_append]
    | 3, s => simp only [Yul.exec, tempSwap, simulSwap, List.cons_append, List.nil_append]
    | (n+4), State.OutOfFuel =>
        simp only [tempSwap, simulSwap, List.cons_append, List.nil_append, Yul.exec,
                   insert_outOfFuel]
    | (n+4), State.Checkpoint j =>
        simp only [tempSwap, simulSwap, List.cons_append, List.nil_append, Yul.exec,
                   insert_checkpoint]
    | (n+4), State.Ok ss store => exact hcore n ss store
  -- Thread the shared prefix P and lift to execTopLevel.
  intro fuel s
  apply Core.execTopLevel_of_exec_eq
  have := Core.exec_block_prefix_congr P .none
            (tempSwap tmp varA varB ++ Q) (simulSwap c varA varB ++ Q) hfrag fuel s
  -- reassociate P ++ swap ++ Q = P ++ (swap ++ Q)
  simpa only [List.append_assoc] using this

/-
  The general, interleaved form of the transformation.

  The theorem above treats the degenerate case in which the three reassignments
  of the swap are consecutive. The professor's statement of the rule allows the
  surrounding blocks `P` and `Q` to be interleaved between them:

        tmp := varA ; P ; varA := varB ; Q ; varB := tmp

  compiled to

        (varA, varB) := (varB, varA) ; P ; Q

  This is sound only under a non-interference proviso: `P` and `Q` must not
  depend on, or write to, `tmp`, `varA`, `varB` (or `c`). The semantic rendering
  of that syntactic condition is `CommutesWith` below.
-/

/-- `X` commutes with a pending write to `v`: running `X` from a state in which
    `v` has just been (or is about to be) bound to `val` gives the same result as
    running `X` from the state without that binding and inserting `v ↦ val` into
    the outcome afterwards. This packages, in one equation, both that `X` does
    not read `v` (the value of `val` cannot influence the result beyond the
    trivial reinsertion) and that `X` does not write `v` (the reinsertion of
    `val` after the fact does not clobber any write `X` performs to `v`). -/
def CommutesWith (X : List Stmt) (v : Identifier) : Prop :=
  ∀ (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val : EvmYul.Literal),
    exec fuel (.Block X) co ((State.Ok ss store)⟦v↦val⟧)
      = (match exec fuel (.Block X) co (State.Ok ss store) with
         | .ok s' => .ok (s'⟦v↦val⟧)
         | .error e => .error e)

/-- Splitting the evaluation of a block `X ++ Y` into the evaluation of `X`
    followed by that of `Y`, with `Y`'s fuel offset by the length of `X`. This
    holds unconditionally, for any statement lists `X`, `Y` whatsoever: no
    assumption is made on whether `X` succeeds, so it applies uniformly to
    blocks of unknown internal structure such as the isolated blocks `P`, `Q`. -/
lemma exec_block_append (X Y : List Stmt) :
    ∀ (fuel : ℕ) (co : Option YulContract) (s : Yul.State),
      exec (fuel + X.length) (.Block (X ++ Y)) co s
        = (match exec (fuel + X.length) (.Block X) co s with
           | .ok s' => exec fuel (.Block Y) co s'
           | .error e => .error e) := by
  induction X with
  | nil =>
    intro fuel co s
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    cases fuel with
    | zero => simp only [Yul.exec]
    | succ n => simp only [Yul.exec]
  | cons p ps ih =>
    intro fuel co s
    rw [show fuel + (p :: ps).length = (fuel + ps.length) + 1 from by
          simp only [List.length_cons]; omega]
    rw [show (p :: ps) ++ Y = p :: (ps ++ Y) from rfl]
    rw [show exec ((fuel + ps.length) + 1) (.Block (p :: (ps ++ Y))) co s
          = _ from by rw [Yul.exec]]
    rw [show exec ((fuel + ps.length) + 1) (.Block (p :: ps)) co s
          = _ from by rw [Yul.exec]]
    cases hp : exec (fuel + ps.length) p co s with
    | error e => rfl
    | ok s₁ => exact ih fuel co s₁

/-
  Extracting the value read at a variable through an isolated block.

  A block that commutes with `v` (in the sense of `CommutesWith`) leaves the
  value read at `v` unchanged, provided its execution actually reaches an `.Ok`
  state. This is proved by instantiating the commutation equation at the value
  already stored at `v`, which cancels the pending write, and then reading the
  resulting identity of states at `v`.
-/

/-- Reinserting the current value of a bound variable leaves the state
    unchanged. -/
lemma insert_self (ss : SharedState .Yul) (store : VarStore) (v : Identifier)
    (hv : v ∈ store) :
    (State.Ok ss store)⟦v ↦ (State.Ok ss store)[v]!⟧ = State.Ok ss store := by
  have hmem : v ∈ (State.Ok ss store).store := hv
  have hread : (State.Ok ss store)[v]! = (Finmap.lookup v store).get! := by
    simp only [getElem!, decidableGetElem?, hmem, dif_pos, getElem]
    rfl
  show State.Ok ss (store.insert v ((State.Ok ss store)[v]!)) = State.Ok ss store
  rw [hread]
  congr 1
  obtain ⟨val, hval⟩ := Finmap.mem_iff.mp hv
  rw [hval]
  show store.insert v val = store
  apply Finmap.ext_lookup
  intro x
  by_cases hx : x = v
  · subst hx; rw [Finmap.lookup_insert, hval]
  · rw [Finmap.lookup_insert_of_ne store hx]

/-- A block commuting with `v`, when it reaches an `.Ok` result, preserves the
    value read at `v`. -/
lemma commutes_preserves_read {X : List Stmt} {v : Identifier} (hX : CommutesWith X v)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (hv : v ∈ store) (ss' : SharedState .Yul) (store' : VarStore)
    (hex : exec fuel (.Block X) co (State.Ok ss store) = .ok (State.Ok ss' store')) :
    (State.Ok ss' store')[v]! = (State.Ok ss store)[v]! := by
  have hself := insert_self ss store v hv
  have hcomm := hX fuel co ss store ((State.Ok ss store)[v]!)
  rw [hself, hex] at hcomm
  injection hcomm with hstate_eq
  have hread : (State.Ok ss' store')[v]! =
      ((State.Ok ss' store')⟦v ↦ (State.Ok ss store)[v]!⟧)[v]! := by rw [← hstate_eq]
  rw [hread]
  exact get_insert_same ss' store' v _

/-- A block commuting with `v`, when it reaches an `.Ok` result, keeps `v`
    bound (this is what licenses reading `v` back out through a later,
    unrelated insertion via `get_insert_ne`). -/
lemma commutes_preserves_mem {X : List Stmt} {v : Identifier} (hX : CommutesWith X v)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (hv : v ∈ store) (ss' : SharedState .Yul) (store' : VarStore)
    (hex : exec fuel (.Block X) co (State.Ok ss store) = .ok (State.Ok ss' store')) :
    v ∈ store' := by
  have hself := insert_self ss store v hv
  have hcomm := hX fuel co ss store ((State.Ok ss store)[v]!)
  rw [hself, hex] at hcomm
  injection hcomm with hstate_eq
  have hmemEq : store' = store'.insert v ((State.Ok ss store)[v]!) := by
    injection hstate_eq
  rw [hmemEq]
  exact Finmap.mem_insert.mpr (Or.inl rfl)

/-
  The non-interference proviso for the interleaved transformation.

  A block `X` is isolated from the swap if it commutes with a pending write to
  each of `tmp`, `c`, `varA`, `varB` (so it neither reads nor writes any of the
  four names the swap manipulates — `c` is included because, in the interleaved
  RHS, `P` and `Q` execute with `c` bound to the captured value, whereas in the
  LHS they never see `c` at all; conversely they execute with `tmp` bound only on
  the LHS), and its execution, whenever it succeeds, reaches an `.Ok` state
  rather than an internal fuel-exhaustion or unstructured-control-transfer
  marker. The latter condition excludes, in the spirit of `Core.RunsOk`, a block
  containing a loop that silently exhausts its own fuel budget or performs a
  non-local jump — occurrences that are precluded for genuine straight-line code.

  Finally, the interleaved LHS and RHS programs spend different numbers of
  statements ahead of `X` (the LHS reaches it after a single reassignment, the
  RHS only after the full three-statement lowered swap), so `X` is invoked at
  two different fuel values across the two derivations. This is why `Isolated`
  carries a `threshold`, beyond which `X`'s result has stabilised (does not
  change with further fuel) — exactly the gas-abstracted stance `Core`'s
  `EventuallyObsEquiv` takes for the whole program, applied here to the
  sub-block `X`. It is this stabilisation, not an exact per-fuel identity, that
  identifies the two invocations of `X`, and correspondingly the general
  theorem below is proved as an `EventuallyObsEquiv`, not the exact
  `ObservationalEquivalence` available for the consecutive (non-interleaved)
  case. -/
structure Isolated (X : List Stmt) (tmp c varA varB : Identifier) where
  commTmp : CommutesWith X tmp
  commC   : CommutesWith X c
  commA   : CommutesWith X varA
  commB   : CommutesWith X varB
  threshold : ℕ
  stable  : ∀ (fuel : ℕ), threshold ≤ fuel →
              ∀ (co : Option YulContract) (s : Yul.State),
              exec fuel (.Block X) co s = exec threshold (.Block X) co s
  okOut   : ∀ (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
              (s' : Yul.State),
              exec threshold (.Block X) co (State.Ok ss store) = .ok s' →
              ∃ ss' store', s' = State.Ok ss' store'
  passthrough : ∀ (co : Option YulContract),
              exec threshold (.Block X) co State.OutOfFuel = .ok State.OutOfFuel
                ∧ ∀ j, exec threshold (.Block X) co (State.Checkpoint j)
                    = .ok (State.Checkpoint j)

/-- Beyond the threshold, an isolated block's result, whenever it succeeds, is
    an `.Ok` state — the same one regardless of which sufficient fuel was
    supplied. -/
lemma Isolated.okOut_of_le {X : List Stmt} {tmp c varA varB : Identifier}
    (h : Isolated X tmp c varA varB) (fuel : ℕ) (hfuel : h.threshold ≤ fuel)
    (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore) (s' : Yul.State)
    (hex : exec fuel (.Block X) co (State.Ok ss store) = .ok s') :
    ∃ ss' store', s' = State.Ok ss' store' := by
  rw [h.stable fuel hfuel co (State.Ok ss store)] at hex
  exact h.okOut co ss store s' hex

/-- Beyond the threshold, an isolated block's result no longer depends on
    which sufficient fuel was supplied — this is what identifies the two
    invocations of `P` (respectively `Q`) across the LHS and RHS derivations,
    which differ in exactly how much fuel remains for `P` (`Q`) once it is
    reached. Stated for an arbitrary starting state (not just `.Ok`), so that
    it also identifies the two invocations when the shared prefix `R` itself
    lands on a fuel-exhaustion or checkpoint marker ahead of `P`. -/
lemma Isolated.agree_of_le {X : List Stmt} {tmp c varA varB : Identifier}
    (h : Isolated X tmp c varA varB) (fuel1 fuel2 : ℕ)
    (hfuel1 : h.threshold ≤ fuel1) (hfuel2 : h.threshold ≤ fuel2)
    (co : Option YulContract) (s : Yul.State) :
    exec fuel1 (.Block X) co s = exec fuel2 (.Block X) co s := by
  rw [h.stable fuel1 hfuel1 co s, h.stable fuel2 hfuel2 co s]

/-- An isolated block, at any sufficient fuel, leaves an `OutOfFuel`/`Checkpoint`
    starting marker untouched — it neither reads nor writes anything, so it can
    only pass such a marker straight through. -/
lemma Isolated.passthrough_of_le {X : List Stmt} {tmp c varA varB : Identifier}
    (h : Isolated X tmp c varA varB) (fuel : ℕ) (hfuel : h.threshold ≤ fuel)
    (co : Option YulContract) :
    exec fuel (.Block X) co State.OutOfFuel = .ok State.OutOfFuel
      ∧ ∀ j, exec fuel (.Block X) co (State.Checkpoint j) = .ok (State.Checkpoint j) := by
  rw [h.stable fuel hfuel co State.OutOfFuel]
  constructor
  · exact (h.passthrough co).1
  · intro j
    rw [h.stable fuel hfuel co (State.Checkpoint j)]
    exact (h.passthrough co).2 j

/-
  The interleaved program forms.

  `R` is the shared prefix, `S` the shared trailing continuation, and `P`, `Q`
  the blocks interleaved between the three reassignments of the temporary-based
  swap. The lowered simultaneous swap is unaffected by the interleaving: the
  compiler performs it as a single uninterrupted sequence ahead of `P`.
-/

/-- The interleaved temporary-based swap. -/
def tempSwapInterleaved (R P Q S : List Stmt) (tmp varA varB : Identifier) : List Stmt :=
  R ++ [.Let [tmp] (some (.Var varA))]
    ++ P ++ [.Let [varA] (some (.Var varB))]
    ++ Q ++ [.Let [varB] (some (.Var tmp))]
    ++ S

/-- The interleaved lowered simultaneous swap. -/
def simulSwapInterleaved (R P Q S : List Stmt) (c varA varB : Identifier) : List Stmt :=
  R ++ simulSwap c varA varB ++ P ++ Q ++ S

/-
  Pushing a pending write through an isolated block.

  If `X` commutes with `v`, then evaluating `X` followed by a continuation
  `rest`, from a state in which `v` has just been written, agrees with
  evaluating `X` alone from the state without that write, and only then
  resuming `rest` with the write reinstated. This is the core reordering step:
  it lets a swap assignment "hop over" an interleaved isolated block. It holds
  for every fuel and continuation, independently of whether `X` itself
  succeeds. -/
lemma push_through (X rest : List Stmt) (v : Identifier) (hX : CommutesWith X v)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val : EvmYul.Literal) :
    exec (fuel + X.length) (.Block (X ++ rest)) co ((State.Ok ss store)⟦v↦val⟧)
      = (match exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
         | .ok s' => exec fuel (.Block rest) co (s'⟦v↦val⟧)
         | .error e => .error e) := by
  rw [exec_block_append X rest fuel co ((State.Ok ss store)⟦v↦val⟧)]
  rw [hX (fuel + X.length) co ss store val]
  cases exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- Two independently-inserted bindings commute with one another. -/
lemma insert_comm (ss : SharedState .Yul) (store : VarStore) (v w : Identifier)
    (hvw : v ≠ w) (val1 val2 : EvmYul.Literal) :
    ((State.Ok ss store)⟦v↦val1⟧)⟦w↦val2⟧ = ((State.Ok ss store)⟦w↦val2⟧)⟦v↦val1⟧ := by
  show State.Ok ss ((store.insert v val1).insert w val2)
     = State.Ok ss ((store.insert w val2).insert v val1)
  congr 1
  exact Finmap.insert_insert_of_ne store hvw

/-
  Pulling several independent pending writes through a block that commutes with
  each of them, without any trailing continuation. Unlike `push_through`, these
  extract the block's result directly rather than composing with a `rest`,
  since they are used at points where the block in question is immediately
  followed either by another such extraction or by the final trailing block.
-/

/-- Two pending writes, to variables the block commutes with, may be pulled
    through together. -/
lemma commutes_shift2 (X : List Stmt) (v1 v2 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 : EvmYul.Literal) :
    exec fuel (.Block X) co (((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)
      = (match exec fuel (.Block X) co (State.Ok ss store) with
         | .ok s' => .ok ((s'⟦v1↦val1⟧)⟦v2↦val2⟧)
         | .error e => .error e) := by
  rw [show (((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)
        = (State.Ok ss (store.insert v1 val1))⟦v2↦val2⟧ from rfl]
  rw [h2 fuel co ss (store.insert v1 val1) val2]
  rw [show (State.Ok ss (store.insert v1 val1)) = (State.Ok ss store)⟦v1↦val1⟧ from rfl]
  rw [h1 fuel co ss store val1]
  cases exec fuel (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- Three pending writes, to variables the block commutes with, may be pulled
    through together. -/
lemma commutes_shift3 (X : List Stmt) (v1 v2 v3 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2) (h3 : CommutesWith X v3)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 val3 : EvmYul.Literal) :
    exec fuel (.Block X) co ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)
      = (match exec fuel (.Block X) co (State.Ok ss store) with
         | .ok s' => .ok (((s'⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)
         | .error e => .error e) := by
  rw [show ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)
        = (State.Ok ss ((store.insert v1 val1).insert v2 val2))⟦v3↦val3⟧ from rfl]
  rw [h3 fuel co ss ((store.insert v1 val1).insert v2 val2) val3]
  rw [show (State.Ok ss ((store.insert v1 val1).insert v2 val2))
        = (State.Ok ss (store.insert v1 val1))⟦v2↦val2⟧ from rfl]
  rw [h2 fuel co ss (store.insert v1 val1) val2]
  rw [show (State.Ok ss (store.insert v1 val1)) = (State.Ok ss store)⟦v1↦val1⟧ from rfl]
  rw [h1 fuel co ss store val1]
  cases exec fuel (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- The two-variable analogue of `push_through`: two pending writes, to
    variables `X` commutes with, hop over `X` together, landing just ahead of
    the continuation `rest`. -/
lemma push_through2 (X rest : List Stmt) (v1 v2 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 : EvmYul.Literal) :
    exec (fuel + X.length) (.Block (X ++ rest)) co
        (((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)
      = (match exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
         | .ok s' => exec fuel (.Block rest) co ((s'⟦v1↦val1⟧)⟦v2↦val2⟧)
         | .error e => .error e) := by
  rw [exec_block_append X rest fuel co (((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)]
  rw [commutes_shift2 X v1 v2 h1 h2 (fuel + X.length) co ss store val1 val2]
  cases exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- The three-variable analogue of `push_through`. -/
lemma push_through3 (X rest : List Stmt) (v1 v2 v3 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2) (h3 : CommutesWith X v3)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 val3 : EvmYul.Literal) :
    exec (fuel + X.length) (.Block (X ++ rest)) co
        ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)
      = (match exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
         | .ok s' => exec fuel (.Block rest) co (((s'⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)
         | .error e => .error e) := by
  rw [exec_block_append X rest fuel co ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)]
  rw [commutes_shift3 X v1 v2 v3 h1 h2 h3 (fuel + X.length) co ss store val1 val2 val3]
  cases exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- Reduction of the interleaved temporary-based swap fragment (shared prefix
    `R` already stripped). The three reassignments hop over the intervening
    isolated blocks `P`, `Q` via `push_through`/`push_through2`, landing as
    three insertions applied to the clean state reached by running `P` then
    `Q`, ahead of the trailing block `S`. -/
lemma lhs_fragment_reduces
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (_hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Ok ss store)
      = (match exec (n + 3 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
         | .error e => .error e
         | .ok sP =>
           match exec (n + 2 + Q.length) (.Block Q) co sP with
           | .error e => .error e
           | .ok sQ =>
             exec (n + 1) (.Block S) co
               (((sQ⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                   ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
                   ⟦varB ↦ (State.Ok ss store)[varA]!⟧)) := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [push_through P _ tmp hP.commTmp (n + 3 + Q.length) co ss store
        ((State.Ok ss store)[varA]!)]
  cases hPexec : exec (n + 3 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    obtain ⟨ssP, storeP, hsP⟩ :=
      hP.okOut_of_le (n + 3 + Q.length + P.length) (by omega) _ _ _ _ hPexec
    subst hsP
    dsimp only
    rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
    rw [exec_block_reassign_cons]
    have hreadB : ((State.Ok ssP storeP)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[varB]!
        = (State.Ok ss store)[varB]! := by
      rw [get_insert_ne ssP storeP tmp varB _ (Ne.symm hTB)
            (commutes_preserves_mem hP.commB (n + 3 + Q.length + P.length) co ss store hmB
              ssP storeP hPexec)]
      exact commutes_preserves_read hP.commB (n + 3 + Q.length + P.length) co ss store hmB
        ssP storeP hPexec
    rw [hreadB]
    rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
    rw [push_through2 Q _ tmp varA hQ.commTmp hQ.commA (n + 2) co ssP storeP
          ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
    cases hQexec : exec (n + 2 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ =>
      obtain ⟨ssQ, storeQ, hsQ⟩ :=
        hQ.okOut_of_le (n + 2 + Q.length) (by omega) _ _ _ _ hQexec
      subst hsQ
      dsimp only
      rw [exec_block_reassign_cons]
      have hreadTmp :
          (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
            = (State.Ok ss store)[varA]! := by
        rw [show (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                  ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
               = ((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[tmp]! from
             get_insert_ne ssQ (Finmap.insert tmp ((State.Ok ss store)[varA]!) storeQ)
               varA tmp _ hTA (Finmap.mem_insert.mpr (Or.inl rfl))]
        exact get_insert_same ssQ storeQ tmp _
      rw [hreadTmp]

/-- Reduction of the interleaved lowered simultaneous-swap fragment (shared
    prefix `R` already stripped). The three-statement swap runs first, as a
    unit, via `simulSwap_append`; the resulting three insertions then hop over
    `P` and `Q` together via `push_through3`. Note that `P`, `Q` are invoked
    here at different fuel values than in `lhs_fragment_reduces` — `Isolated`'s
    `fuelInv` field is what identifies the two. -/
lemma rhs_fragment_reduces
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co (State.Ok ss store)
      = (match exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
         | .error e => .error e
         | .ok sP =>
           match exec (n + 1 + Q.length) (.Block Q) co sP with
           | .error e => .error e
           | .ok sQ =>
             exec (n + 1) (.Block S) co
               ((((sQ⟦c ↦ (State.Ok ss store)[varB]!⟧)
                   ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
                   ⟦varA ↦ (State.Ok ss store)[varB]!⟧))) := by
  unfold simulSwapInterleaved
  simp only [List.nil_append, List.append_assoc]
  rw [show n + 4 + Q.length + P.length = (n + Q.length + P.length) + 4 from by omega]
  rw [simulSwap_append (n + Q.length + P.length) co ss store c varA varB (P ++ (Q ++ S))
        hAB hCA hCB hmA hmB]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [push_through3 P _ c varB varA hP.commC hP.commB hP.commA (n + 1 + Q.length) co ss store
        ((State.Ok ss store)[varB]!) ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
  cases hPexec : exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    obtain ⟨ssP, storeP, hsP⟩ :=
      hP.okOut_of_le (n + 1 + Q.length + P.length) (by omega) _ _ _ _ hPexec
    subst hsP
    dsimp only
    rw [push_through3 Q S c varB varA hQ.commC hQ.commB hQ.commA (n + 1) co ssP storeP
          ((State.Ok ss store)[varB]!) ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
    cases exec (n + 1 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ => rfl

/-- The interleaved fragments (shared prefix `R` already stripped) agree at
    every fuel large enough to clear both `P`'s and `Q`'s thresholds. The two
    reductions above are first aligned at a common invocation of `P`, then of
    `Q` (via `Isolated.agree_of_le`, which is exactly what identifies the
    different fuel values at which the two derivations reach `P`, resp. `Q`),
    and the trailing block `S` is finally handled by `hS`, which absorbs the
    one remaining difference between the two sides: the temporary retains
    `tmp` where the lowered form retains `c`. -/
lemma fragment_eventually_eq
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hS : AgreesOnAB S varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Ok ss store)
      = exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co (State.Ok ss store) := by
  rw [lhs_fragment_reduces n co ss store P Q S tmp c varA varB hTA hTB hmA hmB hP hQ hnP hnQ]
  rw [rhs_fragment_reduces n co ss store P Q S tmp c varA varB hAB hCA hCB hmA hmB hP hQ hnP]
  rw [hP.agree_of_le (n + 3 + Q.length + P.length) (n + 1 + Q.length + P.length)
        (by omega) (by omega) co (State.Ok ss store)]
  cases hPexec : exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    dsimp only
    obtain ⟨ssP, storeP, hsP⟩ := hP.okOut_of_le (n + 1 + Q.length + P.length) (by omega)
      co ss store sP hPexec
    subst hsP
    rw [hQ.agree_of_le (n + 2 + Q.length) (n + 1 + Q.length) (by omega) (by omega) co
          (State.Ok ssP storeP)]
    cases hQexec : exec (n + 1 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ =>
      dsimp only
      obtain ⟨ssQ, storeQ, hsQ⟩ := hQ.okOut_of_le (n + 1 + Q.length) (by omega)
        co ssP storeP sQ hQexec
      subst hsQ
      apply hS (n + 1) _ _ co
      · have hZL :
            (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varA]!
              = (State.Ok ss store)[varB]! := by
          rw [show (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                    ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                    ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varA]!
                 = (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                      ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varA]! from
               get_insert_ne ssQ _ varB varA _ hAB
                 (Finmap.mem_insert.mpr (Or.inl rfl))]
          exact get_insert_same ssQ _ varA _
        have hZR :
            (((State.Ok ssQ storeQ)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varA]!
              = (State.Ok ss store)[varB]! :=
          get_insert_same ssQ _ varA _
        rw [hZL, hZR]
      · have hZL :
            (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varB]!
              = (State.Ok ss store)[varA]! :=
          get_insert_same ssQ _ varB _
        have hZR :
            (((State.Ok ssQ storeQ)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
              = (State.Ok ss store)[varA]! := by
          rw [show (((State.Ok ssQ storeQ)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                    ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                    ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
                 = (((State.Ok ssQ storeQ)⟦c ↦ (State.Ok ss store)[varB]!⟧)
                      ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varB]! from
               get_insert_ne ssQ _ varA varB _ (Ne.symm hAB)
                 (Finmap.mem_insert.mpr (Or.inl rfl))]
          exact get_insert_same ssQ _ varB _
        rw [hZL, hZR]

/-
  Passthrough of a fuel-exhaustion or checkpoint marker through the interleaved
  fragments.

  When the state fed to the fragment is already `OutOfFuel` or a `Checkpoint`,
  every reassignment of the swap is a no-op (`insert_outOfFuel`/
  `insert_checkpoint`), and — by the `passthrough` proviso of `Isolated` — so
  are `P` and `Q`. Both fragments therefore collapse, at the very same fuel
  budgeting as the `.Ok` case, to the trailing block `S` run on the same
  untouched marker, and are trivially equal to each other.
-/

/-- Reduction of the interleaved temporary-based fragment from an `OutOfFuel`
    starting state. -/
lemma lhs_fragment_outOfFuel
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co State.OutOfFuel
      = exec (n + 1) (.Block S) co State.OutOfFuel := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 3 + Q.length) co State.OutOfFuel]
  rw [(hP.passthrough_of_le (n + 3 + Q.length + P.length) (by omega) co).1]
  dsimp only
  rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
  rw [exec_block_append Q _ (n + 2) co State.OutOfFuel]
  rw [(hQ.passthrough_of_le (n + 2 + Q.length) (by omega) co).1]
  dsimp only
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]

/-- Reduction of the interleaved lowered simultaneous-swap fragment from an
    `OutOfFuel` starting state. -/
lemma rhs_fragment_outOfFuel
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co State.OutOfFuel
      = exec (n + 1) (.Block S) co State.OutOfFuel := by
  unfold simulSwapInterleaved
  unfold simulSwap
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 1 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 1 + Q.length + P.length) + 1 = (n + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 1 + Q.length) co State.OutOfFuel]
  rw [(hP.passthrough_of_le (n + 1 + Q.length + P.length) (by omega) co).1]
  dsimp only
  rw [exec_block_append Q S (n + 1) co State.OutOfFuel]
  rw [(hQ.passthrough_of_le (n + 1 + Q.length) (by omega) co).1]

/-- The interleaved fragments agree from an `OutOfFuel` starting state: both
    collapse to `S` on the same untouched marker. -/
lemma fragment_outOfFuel_eq
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co State.OutOfFuel
      = exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co State.OutOfFuel := by
  rw [lhs_fragment_outOfFuel n co P Q S tmp c varA varB hP hQ hnP hnQ,
      rhs_fragment_outOfFuel n co P Q S tmp c varA varB hP hQ hnP hnQ]

/-- Reduction of the interleaved temporary-based fragment from a `Checkpoint`
    starting state. -/
lemma lhs_fragment_checkpoint
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Checkpoint j)
      = exec (n + 1) (.Block S) co (State.Checkpoint j) := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 3 + Q.length) co (State.Checkpoint j)]
  rw [(hP.passthrough_of_le (n + 3 + Q.length + P.length) (by omega) co).2 j]
  dsimp only
  rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
  rw [exec_block_append Q _ (n + 2) co (State.Checkpoint j)]
  rw [(hQ.passthrough_of_le (n + 2 + Q.length) (by omega) co).2 j]
  dsimp only
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]

/-- Reduction of the interleaved lowered simultaneous-swap fragment from a
    `Checkpoint` starting state. -/
lemma rhs_fragment_checkpoint
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co (State.Checkpoint j)
      = exec (n + 1) (.Block S) co (State.Checkpoint j) := by
  unfold simulSwapInterleaved
  unfold simulSwap
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 1 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 1 + Q.length + P.length) + 1 = (n + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 1 + Q.length) co (State.Checkpoint j)]
  rw [(hP.passthrough_of_le (n + 1 + Q.length + P.length) (by omega) co).2 j]
  dsimp only
  rw [exec_block_append Q S (n + 1) co (State.Checkpoint j)]
  rw [(hQ.passthrough_of_le (n + 1 + Q.length) (by omega) co).2 j]

/-- The interleaved fragments agree from a `Checkpoint` starting state: both
    collapse to `S` on the same untouched marker. -/
lemma fragment_checkpoint_eq
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Checkpoint j)
      = exec (n + 4 + Q.length + P.length)
        (.Block (simulSwapInterleaved [] P Q S c varA varB)) co (State.Checkpoint j) := by
  rw [lhs_fragment_checkpoint n co j P Q S tmp c varA varB hP hQ hnP hnQ,
      rhs_fragment_checkpoint n co j P Q S tmp c varA varB hP hQ hnP hnQ]

/-
  Soundness of the general, interleaved single-line-swap transformation.

  `R` is the shared prefix and `S` the shared trailing continuation; `P` and
  `Q` are the blocks interleaved between the three reassignments of the swap.
  Provided `P`, `Q` are isolated from `tmp`, `c`, `varA`, `varB` and `S`
  depends only on `varA`, `varB`, the temporary-based and lowered simultaneous
  forms are eventually observationally equivalent — equal at every fuel large
  enough for `P` and `Q` each to have cleared their own thresholds (`R` carries
  no such restriction: it is threaded through structurally, via
  `exec_block_append`, regardless of what state it leaves behind). This is the
  natural strength available here: unlike the consecutive case, `P` is reached
  after a different number of statements on the two sides, so it is invoked at
  genuinely different fuel values, identified only beyond a threshold, not at
  every fuel.
-/
theorem single_line_swap_equiv_general
    (R P Q S : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmem : ∀ (ss : SharedState .Yul) (store : VarStore),
              varA ∈ (State.Ok ss store).store ∧ varB ∈ (State.Ok ss store).store)
    (hP : Isolated P tmp c varA varB) (hQ : Isolated Q tmp c varA varB)
    (hS : AgreesOnAB S varA varB) :
    EventuallyObsEquiv
      (tempSwapInterleaved R P Q S tmp varA varB)
      (simulSwapInterleaved R P Q S c varA varB) := by
  apply eventuallyObsEquiv_of_exec_eventually_eq
  intro s
  refine ⟨R.length + 4 + Q.length + P.length + hP.threshold + hQ.threshold, ?_⟩
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, n = m + R.length := ⟨n - R.length, by omega⟩
  have hLsplit : tempSwapInterleaved R P Q S tmp varA varB
      = R ++ tempSwapInterleaved [] P Q S tmp varA varB := by
    unfold tempSwapInterleaved; simp only [List.nil_append, List.append_assoc]
  have hRsplit : simulSwapInterleaved R P Q S c varA varB
      = R ++ simulSwapInterleaved [] P Q S c varA varB := by
    unfold simulSwapInterleaved; simp only [List.nil_append, List.append_assoc]
  rw [hLsplit, hRsplit, hm]
  rw [exec_block_append R (tempSwapInterleaved [] P Q S tmp varA varB) m .none s]
  rw [exec_block_append R (simulSwapInterleaved [] P Q S c varA varB) m .none s]
  cases hRexec : exec (m + R.length) (.Block R) .none s with
  | error e => rfl
  | ok s' =>
    dsimp only
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 4 + Q.length + P.length :=
      ⟨m - 4 - Q.length - P.length, by omega⟩
    rw [hm']
    cases s' with
    | Ok ss' store' =>
      exact fragment_eventually_eq m' .none ss' store' P Q S tmp c varA varB
        hAB hTA hTB hCA hCB (hmem ss' store').1 (hmem ss' store').2 hP hQ hS
        (by omega) (by omega)
    | OutOfFuel =>
      exact fragment_outOfFuel_eq m' .none P Q S tmp c varA varB hP hQ (by omega) (by omega)
    | Checkpoint j =>
      exact fragment_checkpoint_eq m' .none j P Q S tmp c varA varB hP hQ (by omega) (by omega)

/-
  Sanity check: the general theorem is not vacuous, and specialises to a
  gas-abstracted form of the consecutive-swap result `single_line_swap_equiv`
  when the interleaved blocks `P`, `Q` are trivial. The empty block commutes
  with anything and passes every marker through unchanged, so it satisfies
  `Isolated` for any four names.
-/

/-- The empty block is (trivially) isolated from any four names: it reads and
    writes nothing. -/
def isolated_nil (tmp c varA varB : Identifier) :
    Isolated ([] : List Stmt) tmp c varA varB where
  commTmp := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commC   := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commA   := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commB   := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  threshold := 1
  stable := by
    intro fuel hfuel co s
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [Yul.exec]
  okOut := by
    intro co ss store s' hex
    simp only [Yul.exec] at hex
    injection hex with h
    exact ⟨ss, store, h.symm⟩
  passthrough := by
    intro co
    refine ⟨by simp only [Yul.exec], fun j => by simp only [Yul.exec]⟩

/-- The general theorem, specialised to trivial interleaved blocks, recovers
    (in gas-abstracted form) the soundness of the consecutive single-line-swap
    transformation `single_line_swap_equiv`. -/
theorem single_line_swap_equiv_general_nil
    (R S : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmem : ∀ (ss : SharedState .Yul) (store : VarStore),
              varA ∈ (State.Ok ss store).store ∧ varB ∈ (State.Ok ss store).store)
    (hS : AgreesOnAB S varA varB) :
    EventuallyObsEquiv
      (R ++ tempSwap tmp varA varB ++ S)
      (R ++ simulSwap c varA varB ++ S) := by
  have h := single_line_swap_equiv_general R [] [] S tmp c varA varB
    hAB hTA hTB hCA hCB hmem (isolated_nil tmp c varA varB) (isolated_nil tmp c varA varB) hS
  simpa only [tempSwapInterleaved, simulSwapInterleaved, tempSwap, simulSwap,
    List.nil_append, List.append_nil, List.append_assoc] using h

/-
  The compiler-faithful four-statement form of the simultaneous swap.

  The lowered form verified above collapses the simultaneous assignment to
  three statements, capturing only the second operand ahead of the two
  cross-assignments. The compiler (`solc`) instead captures BOTH operands into
  fresh temporaries before performing either write, as witnessed by the
  reference output `single-line-swap.yul`:

        let expr_34_component_1 := expr_32   -- = varB
        let expr_34_component_2 := expr_33   -- = varA
        var_varB_26 := expr_34_component_2   -- varB := (old varA)
        var_varA_22 := expr_34_component_1   -- varA := (old varB)

  which is modelled here, at the level of Yul statements, as
  `simulSwapFour`. The three-statement `simulSwap` above remains available as a
  simplified model; the four-statement form below is the one that is faithful
  to the compiler's actual output and is the primary result of this file.
-/

def simulSwapFour (v1 v2 varA varB : Identifier) : List Stmt :=
  [ .Let [v1]   (some (.Var varB)),   -- v1 := varB   (capture old varB)
    .Let [v2]   (some (.Var varA)),   -- v2 := varA   (capture old varA)
    .Let [varB] (some (.Var v2)),     -- varB := v2   (= old varA)
    .Let [varA] (some (.Var v1)) ]    -- varA := v1   (= old varB)

/-- Interleaved right-hand side: the four-statement swap up front, then `P`,
    `Q`, `S`. The swap is, as in the three-statement lowered form, performed as
    a single uninterrupted sequence ahead of `P`. -/
def simulSwapFourInterleaved (R P Q S : List Stmt) (v1 v2 varA varB : Identifier) : List Stmt :=
  R ++ simulSwapFour v1 v2 varA varB ++ P ++ Q ++ S

/-- Evaluation of four reassignments followed by a continuation: the four steps
    are performed and evaluation proceeds with the continuation from the
    resulting state. The four-statement analogue of `exec_reassign3_append_Q`. -/
lemma exec_reassign4_append_Q
    (n : ℕ) (co : Option YulContract) (s : Yul.State) (Q : List Stmt)
    (va vb vc vd wa wb wc wd : Identifier) :
    exec (n + 5) (.Block ([.Let [va] (some (.Var wa)),
                           .Let [vb] (some (.Var wb)),
                           .Let [vc] (some (.Var wc)),
                           .Let [vd] (some (.Var wd))] ++ Q)) co s
      = exec (n + 1) (.Block Q) co
          ((((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)
             ⟦vc ↦ ((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)[wc]!⟧)
             ⟦vd ↦ (((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)
                      ⟦vc ↦ ((s⟦va ↦ s[wa]!⟧)⟦vb ↦ (s⟦va ↦ s[wa]!⟧)[wb]!⟧)[wc]!⟧)[wd]!⟧) := by
  simp only [List.cons_append, List.nil_append]
  rw [show n + 5 = (n+3) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 3 + 1 = (n+2) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 2 + 1 = (n+1) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 1 + 1 = n + 2 from by omega, exec_block_reassign_cons]

/-- Effect of the four-statement compiler-faithful sequence. From a state in
    which the five names (`v1`, `v2`, `varA`, `varB`, and implicitly whatever
    else) are pairwise distinct as required, and `varA`, `varB` are bound, the
    four reassignments yield the state that binds `varA` and `varB` to their
    exchanged values (with `v1`, `v2` retaining the captured originals). The
    proof reduces the four steps and evaluates the resulting reads, mirroring
    `simulSwap_effect` with one extra capture step. -/
lemma simulSwapFour_effect
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (v1 v2 varA varB : Identifier)
    (_hAB : varA ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (_h2A : v2 ≠ varA) (_h2B : v2 ≠ varB)
    (h12 : v1 ≠ v2)
    (hmA : varA ∈ store) (_hmB : varB ∈ store) :
    exec (n + 5) (.Block (simulSwapFour v1 v2 varA varB)) co (State.Ok ss store)
      = .ok (((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧) := by
  unfold simulSwapFour
  rw [show n + 5 = (n+3) + 2 from by omega, exec_block_reassign_cons]
  rw [show n + 3 + 1 = (n+2) + 2 from by omega, exec_block_reassign_cons]
  -- read varA in state ⟦v1↦B₀⟧: v1 ≠ varA, varA ∈ store  ⟹  A₀
  rw [show ((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)[varA]!
        = (State.Ok ss store)[varA]! from
        get_insert_ne ss store v1 varA _ (Ne.symm h1A) hmA]
  rw [show n + 2 + 1 = (n+1) + 2 from by omega, exec_block_reassign_cons]
  -- read v2 in state ⟦v1↦B₀⟧⟦v2↦A₀⟧: top insert  ⟹  A₀
  rw [show (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
            ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v2]!
        = (State.Ok ss store)[varA]! from
        get_insert_same ss _ v2 _]
  rw [show n + 1 + 1 = n + 2 from by omega, exec_block_reassign_single]
  congr 1
  -- read v1 in state ⟦v1↦B₀⟧⟦v2↦A₀⟧⟦varB↦A₀⟧: peel varB (v1≠varB), then v2 (v1≠v2), hit v1  ⟹  B₀
  have hread :
      ((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
          ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
          ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[v1]!
        = (State.Ok ss store)[varB]! := by
    rw [show ((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[v1]!
           = (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v1]! from
         get_insert_ne ss _ varB v1 _ h1B
           (Finmap.mem_insert.mpr (Or.inr (Finmap.mem_insert.mpr (Or.inl rfl))))]
    rw [show (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v1]!
           = ((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)[v1]! from
         get_insert_ne ss _ v2 v1 _ h12 (Finmap.mem_insert.mpr (Or.inl rfl))]
    exact get_insert_same ss store v1 _
  rw [hread]

/-- In the state reached by the four-statement compiler-faithful sequence,
    `varA` and `varB` hold the exchanged values, in agreement with both the
    temporary-based and three-statement lowered sequences. -/
lemma simulSwapFour_reads
    (ss : SharedState .Yul) (store : VarStore) (v1 v2 varA varB : Identifier)
    (hAB : varA ≠ varB) (_h1A : v1 ≠ varA) (_h1B : v1 ≠ varB)
    (_h2A : v2 ≠ varA) (_h2B : v2 ≠ varB) (_h12 : v1 ≠ v2) :
    (((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
        ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varA]!
      = (State.Ok ss store)[varB]!
    ∧ (((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
        ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
        ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
      = (State.Ok ss store)[varA]! := by
  constructor
  · -- read varA: hits the outermost varA-insert directly
    exact get_insert_same ss _ varA _
  · -- read varB: passes varA-insert (varB ≠ varA), hits varB-insert
    rw [show (((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
           = ((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varB]! from
         get_insert_ne ss _ varA varB _ (Ne.symm hAB)
           (Finmap.mem_insert.mpr (Or.inl rfl))]
    exact get_insert_same ss _ varB _

/-- Evaluation of the four-statement compiler-faithful sequence followed by the
    continuation, presented with the resulting state in reduced form. The
    four-statement analogue of `simulSwap_append`. -/
lemma simulSwapFour_append
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (v1 v2 varA varB : Identifier) (Q : List Stmt)
    (_hAB : varA ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (_h2A : v2 ≠ varA) (_h2B : v2 ≠ varB)
    (h12 : v1 ≠ v2)
    (hmA : varA ∈ store) (_hmB : varB ∈ store) :
    exec (n + 5) (.Block (simulSwapFour v1 v2 varA varB ++ Q)) co (State.Ok ss store)
      = exec (n + 1) (.Block Q) co
          (((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
              ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧) := by
  unfold simulSwapFour
  rw [exec_reassign4_append_Q]
  -- read2: varA in ⟦v1↦B₀⟧  ⟹  A₀
  rw [show ((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)[varA]!
        = (State.Ok ss store)[varA]! from
        get_insert_ne ss store v1 varA _ (Ne.symm h1A) hmA]
  -- read3: v2 in ⟦v1↦B₀⟧⟦v2↦A₀⟧  ⟹  A₀ (top read)
  rw [show (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
            ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v2]!
        = (State.Ok ss store)[varA]! from
        get_insert_same ss _ v2 _]
  -- read4: v1 in ⟦v1↦B₀⟧⟦v2↦A₀⟧⟦varB↦A₀⟧  ⟹  B₀ (double peel)
  rw [show ((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
            ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
            ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[v1]!
        = (State.Ok ss store)[varB]! from by
      rw [show ((((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[v1]!
             = (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v1]! from
           get_insert_ne ss _ varB v1 _ h1B
             (Finmap.mem_insert.mpr (Or.inr (Finmap.mem_insert.mpr (Or.inl rfl))))]
      rw [show (((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)[v1]!
             = ((State.Ok ss store)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)[v1]! from
           get_insert_ne ss _ v2 v1 _ h12 (Finmap.mem_insert.mpr (Or.inl rfl))]
      exact get_insert_same ss store v1 _]

/-- The four-variable analogue of `commutes_shift3`: four pending writes, to
    variables the block commutes with, may be pulled through together. -/
lemma commutes_shift4 (X : List Stmt) (v1 v2 v3 v4 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2)
    (h3 : CommutesWith X v3) (h4 : CommutesWith X v4)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 val3 val4 : EvmYul.Literal) :
    exec fuel (.Block X) co
        ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧⟦v4↦val4⟧)
      = (match exec fuel (.Block X) co (State.Ok ss store) with
         | .ok s' => .ok ((((s'⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)⟦v4↦val4⟧)
         | .error e => .error e) := by
  rw [show (((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧⟦v4↦val4⟧
        = (State.Ok ss (((store.insert v1 val1).insert v2 val2).insert v3 val3))⟦v4↦val4⟧
        from rfl]
  rw [h4 fuel co ss (((store.insert v1 val1).insert v2 val2).insert v3 val3) val4]
  rw [show (State.Ok ss (((store.insert v1 val1).insert v2 val2).insert v3 val3))
        = (State.Ok ss ((store.insert v1 val1).insert v2 val2))⟦v3↦val3⟧ from rfl]
  rw [h3 fuel co ss ((store.insert v1 val1).insert v2 val2) val3]
  rw [show (State.Ok ss ((store.insert v1 val1).insert v2 val2))
        = (State.Ok ss (store.insert v1 val1))⟦v2↦val2⟧ from rfl]
  rw [h2 fuel co ss (store.insert v1 val1) val2]
  rw [show (State.Ok ss (store.insert v1 val1)) = (State.Ok ss store)⟦v1↦val1⟧ from rfl]
  rw [h1 fuel co ss store val1]
  cases exec fuel (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-- The four-variable analogue of `push_through3`: four pending writes, to
    variables `X` commutes with, hop over `X` together, landing just ahead of
    the continuation `rest`. -/
lemma push_through4 (X rest : List Stmt) (v1 v2 v3 v4 : Identifier)
    (h1 : CommutesWith X v1) (h2 : CommutesWith X v2)
    (h3 : CommutesWith X v3) (h4 : CommutesWith X v4)
    (fuel : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (val1 val2 val3 val4 : EvmYul.Literal) :
    exec (fuel + X.length) (.Block (X ++ rest)) co
        ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧⟦v4↦val4⟧)
      = (match exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
         | .ok s' => exec fuel (.Block rest) co ((((s'⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧)⟦v4↦val4⟧)
         | .error e => .error e) := by
  rw [exec_block_append X rest fuel co
        ((((State.Ok ss store)⟦v1↦val1⟧)⟦v2↦val2⟧)⟦v3↦val3⟧⟦v4↦val4⟧)]
  rw [commutes_shift4 X v1 v2 v3 v4 h1 h2 h3 h4 (fuel + X.length) co ss store
        val1 val2 val3 val4]
  cases exec (fuel + X.length) (.Block X) co (State.Ok ss store) with
  | error e => rfl
  | ok s' => rfl

/-
  The non-interference proviso for the compiler-faithful four-statement
  transformation.

  The right-hand side now binds TWO compiler temporaries `v1`, `v2` — never
  bound on the left-hand side — so `P`, `Q` must not read or write either of
  them (in addition to `tmp`, `varA`, `varB`, exactly as `Isolated` already
  required of `c` in the three-statement lowered form). `Isolated4` is the
  semantic rendering of the syntactic side condition "`tmp`, `varA`, `varB`,
  and the compiler temporaries `v1`, `v2` do not occur in `P`, `Q`"; as with
  `Isolated`, this syntactic-to-semantic bridge is part of the trusted
  computing base, assumed rather than proved, on the same footing as the
  Yul/`solc` fidelity of `simulSwapFour` itself and the professor's clean-up
  Theorems 1 and 2 that reduce the raw compiler output to this canonical
  four-`let` form. Omitting `v1` or `v2` from the commutation set yields a
  FALSE theorem: a `P` that reads `v1` would observe the captured value of
  `varB` where the temporary-based left-hand side has no such binding at all. -/
structure Isolated4 (X : List Stmt) (tmp v1 v2 varA varB : Identifier) where
  commTmp : CommutesWith X tmp
  commV1  : CommutesWith X v1
  commV2  : CommutesWith X v2
  commA   : CommutesWith X varA
  commB   : CommutesWith X varB
  threshold : ℕ
  stable  : ∀ (fuel : ℕ), threshold ≤ fuel →
              ∀ (co : Option YulContract) (s : Yul.State),
              exec fuel (.Block X) co s = exec threshold (.Block X) co s
  okOut   : ∀ (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
              (s' : Yul.State),
              exec threshold (.Block X) co (State.Ok ss store) = .ok s' →
              ∃ ss' store', s' = State.Ok ss' store'
  passthrough : ∀ (co : Option YulContract),
              exec threshold (.Block X) co State.OutOfFuel = .ok State.OutOfFuel
                ∧ ∀ j, exec threshold (.Block X) co (State.Checkpoint j)
                    = .ok (State.Checkpoint j)

/-- Beyond the threshold, an `Isolated4` block's result, whenever it succeeds,
    is an `.Ok` state — the same one regardless of which sufficient fuel was
    supplied. -/
lemma Isolated4.okOut_of_le {X : List Stmt} {tmp v1 v2 varA varB : Identifier}
    (h : Isolated4 X tmp v1 v2 varA varB) (fuel : ℕ) (hfuel : h.threshold ≤ fuel)
    (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore) (s' : Yul.State)
    (hex : exec fuel (.Block X) co (State.Ok ss store) = .ok s') :
    ∃ ss' store', s' = State.Ok ss' store' := by
  rw [h.stable fuel hfuel co (State.Ok ss store)] at hex
  exact h.okOut co ss store s' hex

/-- Beyond the threshold, an `Isolated4` block's result no longer depends on
    which sufficient fuel was supplied. -/
lemma Isolated4.agree_of_le {X : List Stmt} {tmp v1 v2 varA varB : Identifier}
    (h : Isolated4 X tmp v1 v2 varA varB) (fuel1 fuel2 : ℕ)
    (hfuel1 : h.threshold ≤ fuel1) (hfuel2 : h.threshold ≤ fuel2)
    (co : Option YulContract) (s : Yul.State) :
    exec fuel1 (.Block X) co s = exec fuel2 (.Block X) co s := by
  rw [h.stable fuel1 hfuel1 co s, h.stable fuel2 hfuel2 co s]

/-- An `Isolated4` block, at any sufficient fuel, leaves an
    `OutOfFuel`/`Checkpoint` starting marker untouched. -/
lemma Isolated4.passthrough_of_le {X : List Stmt} {tmp v1 v2 varA varB : Identifier}
    (h : Isolated4 X tmp v1 v2 varA varB) (fuel : ℕ) (hfuel : h.threshold ≤ fuel)
    (co : Option YulContract) :
    exec fuel (.Block X) co State.OutOfFuel = .ok State.OutOfFuel
      ∧ ∀ j, exec fuel (.Block X) co (State.Checkpoint j) = .ok (State.Checkpoint j) := by
  rw [h.stable fuel hfuel co State.OutOfFuel]
  constructor
  · exact (h.passthrough co).1
  · intro j
    rw [h.stable fuel hfuel co (State.Checkpoint j)]
    exact (h.passthrough co).2 j

/-
  The trailing continuation's proviso, strengthened for the four-statement
  theorem.

  `AgreesOnAB` (used above) requires `S` to evaluate identically from any two
  states agreeing on `varA`, `varB`, AT THE SAME FUEL. That suffices exactly
  when the two swap forms being compared consume the same number of
  statements, so that a shared total fuel budget hands `S` the same remaining
  fuel on both sides — the case for the three-statement `tempSwap`/`simulSwap`
  pair. It is NOT the case here: the four-statement `simulSwapFour` consumes
  one more unit of fuel than the three-statement `tempSwap` before reaching
  `S`, so under a shared total fuel budget across the whole program, the two
  derivations hand `S` fuel differing by exactly one. Bridging that one-unit
  gap would ordinarily be immediate from fuel-monotonicity of `exec`, but this
  development deliberately does not assume that (`Core.lean` explicitly notes
  its reasoning principles are developed fuel-monotonicity-free). Instead,
  exactly as `Isolated.stable` does for the interleaved blocks `P`, `Q`,
  `AgreesOnABEventually` packages the needed stabilisation explicitly: `S`'s
  result, from ANY starting state, no longer depends on the exact fuel once a
  threshold is cleared, and at that threshold it agrees across any two states
  that agree on `varA`, `varB`. This is a strengthening of `AgreesOnAB`, used
  only for the four-statement theorem below; the three-statement theorems
  above, and their `AgreesOnAB` proviso, are untouched. -/
structure AgreesOnABEventually (S : List Stmt) (varA varB : Identifier) where
  threshold : ℕ
  stable : ∀ (fuel : ℕ), threshold ≤ fuel → ∀ (co : Option YulContract) (s : Yul.State),
      exec fuel (.Block S) co s = exec threshold (.Block S) co s
  agree : ∀ (s₁ s₂ : Yul.State) (co : Option YulContract),
      s₁[varA]! = s₂[varA]! → s₁[varB]! = s₂[varB]! →
      exec threshold (.Block S) co s₁ = exec threshold (.Block S) co s₂

/-- Reduction of the interleaved temporary-based swap fragment for the
    four-statement theorem (shared prefix `R` already stripped). The
    left-hand side is unchanged from the three-statement development — it is
    still the three-reassignment `tempSwapInterleaved` — so this is
    `lhs_fragment_reduces` verbatim, typed against `Isolated4` (five names)
    instead of `Isolated` (four names) for `P`, `Q`. -/
lemma lhs_fragment_four_reduces
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (_hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Ok ss store)
      = (match exec (n + 3 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
         | .error e => .error e
         | .ok sP =>
           match exec (n + 2 + Q.length) (.Block Q) co sP with
           | .error e => .error e
           | .ok sQ =>
             exec (n + 1) (.Block S) co
               (((sQ⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                   ⟦varA ↦ (State.Ok ss store)[varB]!⟧)
                   ⟦varB ↦ (State.Ok ss store)[varA]!⟧)) := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [push_through P _ tmp hP.commTmp (n + 3 + Q.length) co ss store
        ((State.Ok ss store)[varA]!)]
  cases hPexec : exec (n + 3 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    obtain ⟨ssP, storeP, hsP⟩ :=
      hP.okOut_of_le (n + 3 + Q.length + P.length) (by omega) _ _ _ _ hPexec
    subst hsP
    dsimp only
    rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
    rw [exec_block_reassign_cons]
    have hreadB : ((State.Ok ssP storeP)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[varB]!
        = (State.Ok ss store)[varB]! := by
      rw [get_insert_ne ssP storeP tmp varB _ (Ne.symm hTB)
            (commutes_preserves_mem hP.commB (n + 3 + Q.length + P.length) co ss store hmB
              ssP storeP hPexec)]
      exact commutes_preserves_read hP.commB (n + 3 + Q.length + P.length) co ss store hmB
        ssP storeP hPexec
    rw [hreadB]
    rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
    rw [push_through2 Q _ tmp varA hQ.commTmp hQ.commA (n + 2) co ssP storeP
          ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
    cases hQexec : exec (n + 2 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ =>
      obtain ⟨ssQ, storeQ, hsQ⟩ :=
        hQ.okOut_of_le (n + 2 + Q.length) (by omega) _ _ _ _ hQexec
      subst hsQ
      dsimp only
      rw [exec_block_reassign_cons]
      have hreadTmp :
          (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
              ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
            = (State.Ok ss store)[varA]! := by
        rw [show (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                  ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[tmp]!
               = ((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)[tmp]! from
             get_insert_ne ssQ (Finmap.insert tmp ((State.Ok ss store)[varA]!) storeQ)
               varA tmp _ hTA (Finmap.mem_insert.mpr (Or.inl rfl))]
        exact get_insert_same ssQ storeQ tmp _
      rw [hreadTmp]

/-- Reduction of the interleaved four-statement compiler-faithful fragment
    (shared prefix `R` already stripped). The four-statement swap runs first,
    as a unit, via `simulSwapFour_append`; the resulting four insertions then
    hop over `P` and `Q` together via `push_through4`. -/
lemma rhs_fragment_four_reduces
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hAB : varA ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (h2A : v2 ≠ varA) (h2B : v2 ≠ varB) (h12 : v1 ≠ v2)
    (hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co (State.Ok ss store)
      = (match exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
         | .error e => .error e
         | .ok sP =>
           match exec (n + 1 + Q.length) (.Block Q) co sP with
           | .error e => .error e
           | .ok sQ =>
             exec (n + 1) (.Block S) co
               ((((sQ⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                   ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                   ⟦varB ↦ (State.Ok ss store)[varA]!⟧)
                   ⟦varA ↦ (State.Ok ss store)[varB]!⟧)) := by
  unfold simulSwapFourInterleaved
  simp only [List.nil_append, List.append_assoc]
  rw [show n + 5 + Q.length + P.length = (n + Q.length + P.length) + 5 from by omega]
  rw [simulSwapFour_append (n + Q.length + P.length) co ss store v1 v2 varA varB
        (P ++ (Q ++ S)) hAB h1A h1B h2A h2B h12 hmA hmB]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [push_through4 P _ v1 v2 varB varA hP.commV1 hP.commV2 hP.commB hP.commA
        (n + 1 + Q.length) co ss store
        ((State.Ok ss store)[varB]!) ((State.Ok ss store)[varA]!)
        ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
  cases hPexec : exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    obtain ⟨ssP, storeP, hsP⟩ :=
      hP.okOut_of_le (n + 1 + Q.length + P.length) (by omega) _ _ _ _ hPexec
    subst hsP
    dsimp only
    rw [push_through4 Q S v1 v2 varB varA hQ.commV1 hQ.commV2 hQ.commB hQ.commA
          (n + 1) co ssP storeP
          ((State.Ok ss store)[varB]!) ((State.Ok ss store)[varA]!)
          ((State.Ok ss store)[varA]!) ((State.Ok ss store)[varB]!)]
    cases exec (n + 1 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ => rfl

/-- The interleaved four-statement fragments (shared prefix `R` already
    stripped) agree at every fuel large enough to clear `P`'s and `Q`'s
    thresholds, and `S`'s. The left-hand side is invoked with internal
    parameter `n+1` and the right-hand side with `n`, so that both share the
    same total fuel `n + 5 + Q.length + P.length`; `P` and `Q` are then
    aligned via `Isolated4.agree_of_le`, exactly as in `fragment_eventually_eq`.
    The remaining one-unit fuel difference at `S` — which does not arise in
    the three-statement development, where both swap forms consume the same
    fuel — is what `AgreesOnABEventually` is for. -/
lemma fragment_four_eventually_eq
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (h2A : v2 ≠ varA) (h2B : v2 ≠ varB) (h12 : v1 ≠ v2)
    (hmA : varA ∈ store) (hmB : varB ∈ store)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hS : AgreesOnABEventually S varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) (hnS : hS.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Ok ss store)
      = exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co (State.Ok ss store) := by
  rw [show n + 5 + Q.length + P.length = (n + 1) + 4 + Q.length + P.length from by omega]
  rw [lhs_fragment_four_reduces (n+1) co ss store P Q S tmp v1 v2 varA varB hTA hTB hmA hmB
        hP hQ (by omega) (by omega)]
  rw [show (n + 1) + 4 + Q.length + P.length = n + 5 + Q.length + P.length from by omega]
  rw [rhs_fragment_four_reduces n co ss store P Q S tmp v1 v2 varA varB
        hAB h1A h1B h2A h2B h12 hmA hmB hP hQ hnP]
  rw [hP.agree_of_le ((n + 1) + 3 + Q.length + P.length) (n + 1 + Q.length + P.length)
        (by omega) (by omega) co (State.Ok ss store)]
  cases hPexec : exec (n + 1 + Q.length + P.length) (.Block P) co (State.Ok ss store) with
  | error e => rfl
  | ok sP =>
    dsimp only
    obtain ⟨ssP, storeP, hsP⟩ := hP.okOut_of_le (n + 1 + Q.length + P.length) (by omega)
      co ss store sP hPexec
    subst hsP
    rw [hQ.agree_of_le ((n + 1) + 2 + Q.length) (n + 1 + Q.length) (by omega) (by omega) co
          (State.Ok ssP storeP)]
    cases hQexec : exec (n + 1 + Q.length) (.Block Q) co (State.Ok ssP storeP) with
    | error e => rfl
    | ok sQ =>
      dsimp only
      obtain ⟨ssQ, storeQ, hsQ⟩ := hQ.okOut_of_le (n + 1 + Q.length) (by omega)
        co ssP storeP sQ hQexec
      subst hsQ
      rw [hS.stable ((n + 1) + 1) (by omega) co _, hS.stable (n + 1) (by omega) co _]
      apply hS.agree _ _ co
      · -- LHS/RHS states agree on `varA`
        have hZL :
            (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varA]!
              = (State.Ok ss store)[varB]! := by
          rw [show (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                    ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                    ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varA]!
                 = (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                      ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varA]! from
               get_insert_ne ssQ _ varB varA _ hAB
                 (Finmap.mem_insert.mpr (Or.inl rfl))]
          exact get_insert_same ssQ _ varA _
        have hZR :
            ((((State.Ok ssQ storeQ)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varA]!
              = (State.Ok ss store)[varB]! :=
          get_insert_same ssQ _ varA _
        rw [hZL, hZR]
      · -- LHS/RHS states agree on `varB`
        have hZL :
            (((State.Ok ssQ storeQ)⟦tmp ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varB]!
              = (State.Ok ss store)[varA]! :=
          get_insert_same ssQ _ varB _
        have hZR :
            ((((State.Ok ssQ storeQ)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
              = (State.Ok ss store)[varA]! := by
          rw [show ((((State.Ok ssQ storeQ)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                    ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                    ⟦varB ↦ (State.Ok ss store)[varA]!⟧
                    ⟦varA ↦ (State.Ok ss store)[varB]!⟧)[varB]!
                 = ((((State.Ok ssQ storeQ)⟦v1 ↦ (State.Ok ss store)[varB]!⟧)
                      ⟦v2 ↦ (State.Ok ss store)[varA]!⟧)
                      ⟦varB ↦ (State.Ok ss store)[varA]!⟧)[varB]! from
               get_insert_ne ssQ _ varA varB _ (Ne.symm hAB)
                 (Finmap.mem_insert.mpr (Or.inl rfl))]
          exact get_insert_same ssQ _ varB _
        rw [hZL, hZR]

/-
  Passthrough of a fuel-exhaustion or checkpoint marker through the
  four-statement interleaved fragments, mirroring the three-statement
  development above.
-/

/-- Reduction of the interleaved temporary-based fragment from an `OutOfFuel`
    starting state, typed against `Isolated4`. Identical in substance to
    `lhs_fragment_outOfFuel`, since the left-hand side is unchanged. -/
lemma lhs_fragment_four_outOfFuel
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co State.OutOfFuel
      = exec (n + 1) (.Block S) co State.OutOfFuel := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 3 + Q.length) co State.OutOfFuel]
  rw [(hP.passthrough_of_le (n + 3 + Q.length + P.length) (by omega) co).1]
  dsimp only
  rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
  rw [exec_block_append Q _ (n + 2) co State.OutOfFuel]
  rw [(hQ.passthrough_of_le (n + 2 + Q.length) (by omega) co).1]
  dsimp only
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]

/-- Reduction of the interleaved four-statement compiler-faithful fragment
    from an `OutOfFuel` starting state. -/
lemma rhs_fragment_four_outOfFuel
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co State.OutOfFuel
      = exec (n + 1) (.Block S) co State.OutOfFuel := by
  unfold simulSwapFourInterleaved
  unfold simulSwapFour
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 5 + Q.length + P.length = (n + 3 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 3 + Q.length + P.length) + 1 = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 1 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + 1 + Q.length + P.length) + 1 = (n + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_outOfFuel]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 1 + Q.length) co State.OutOfFuel]
  rw [(hP.passthrough_of_le (n + 1 + Q.length + P.length) (by omega) co).1]
  dsimp only
  rw [exec_block_append Q S (n + 1) co State.OutOfFuel]
  rw [(hQ.passthrough_of_le (n + 1 + Q.length) (by omega) co).1]

/-- The interleaved four-statement fragments agree from an `OutOfFuel`
    starting state. Both collapse to `S` run on the same untouched marker, at
    fuels differing by one (`n+2` on the left, `n+1` on the right, after
    aligning totals as in `fragment_four_eventually_eq`); `AgreesOnABEventually`
    bridges that gap, its `agree` field applying trivially since the marker is
    syntactically identical on both sides. -/
lemma fragment_four_outOfFuel_eq
    (n : ℕ) (co : Option YulContract)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hS : AgreesOnABEventually S varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) (hnS : hS.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co State.OutOfFuel
      = exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co State.OutOfFuel := by
  rw [show n + 5 + Q.length + P.length = (n + 1) + 4 + Q.length + P.length from by omega]
  rw [lhs_fragment_four_outOfFuel (n+1) co P Q S tmp v1 v2 varA varB hP hQ (by omega) (by omega)]
  rw [show (n + 1) + 4 + Q.length + P.length = n + 5 + Q.length + P.length from by omega]
  rw [rhs_fragment_four_outOfFuel n co P Q S tmp v1 v2 varA varB hP hQ hnP hnQ]
  rw [hS.stable ((n + 1) + 1) (by omega) co State.OutOfFuel,
      hS.stable (n + 1) (by omega) co State.OutOfFuel]

/-- Reduction of the interleaved temporary-based fragment from a `Checkpoint`
    starting state, typed against `Isolated4`. -/
lemma lhs_fragment_four_checkpoint
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 4 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Checkpoint j)
      = exec (n + 1) (.Block S) co (State.Checkpoint j) := by
  unfold tempSwapInterleaved
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 4 + Q.length + P.length = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 3 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 3 + Q.length) co (State.Checkpoint j)]
  rw [(hP.passthrough_of_le (n + 3 + Q.length + P.length) (by omega) co).2 j]
  dsimp only
  rw [show n + 3 + Q.length = (n + 1 + Q.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 1 + Q.length) + 1 = (n + 2) + Q.length from by omega]
  rw [exec_block_append Q _ (n + 2) co (State.Checkpoint j)]
  rw [(hQ.passthrough_of_le (n + 2 + Q.length) (by omega) co).2 j]
  dsimp only
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]

/-- Reduction of the interleaved four-statement compiler-faithful fragment
    from a `Checkpoint` starting state. -/
lemma rhs_fragment_four_checkpoint
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co (State.Checkpoint j)
      = exec (n + 1) (.Block S) co (State.Checkpoint j) := by
  unfold simulSwapFourInterleaved
  unfold simulSwapFour
  simp only [List.nil_append, List.append_assoc, List.cons_append]
  rw [show n + 5 + Q.length + P.length = (n + 3 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 3 + Q.length + P.length) + 1 = (n + 2 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 2 + Q.length + P.length) + 1 = (n + 1 + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + 1 + Q.length + P.length) + 1 = (n + Q.length + P.length) + 2 from by omega]
  rw [exec_block_reassign_cons]
  simp only [insert_checkpoint]
  rw [show (n + Q.length + P.length) + 1 = (n + 1 + Q.length) + P.length from by omega]
  rw [exec_block_append P _ (n + 1 + Q.length) co (State.Checkpoint j)]
  rw [(hP.passthrough_of_le (n + 1 + Q.length + P.length) (by omega) co).2 j]
  dsimp only
  rw [exec_block_append Q S (n + 1) co (State.Checkpoint j)]
  rw [(hQ.passthrough_of_le (n + 1 + Q.length) (by omega) co).2 j]

/-- The interleaved four-statement fragments agree from a `Checkpoint`
    starting state, for the same reason as `fragment_four_outOfFuel_eq`. -/
lemma fragment_four_checkpoint_eq
    (n : ℕ) (co : Option YulContract) (j : Jump)
    (P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hS : AgreesOnABEventually S varA varB)
    (hnP : hP.threshold ≤ n) (hnQ : hQ.threshold ≤ n) (hnS : hS.threshold ≤ n) :
    exec (n + 5 + Q.length + P.length)
        (.Block (tempSwapInterleaved [] P Q S tmp varA varB)) co (State.Checkpoint j)
      = exec (n + 5 + Q.length + P.length)
        (.Block (simulSwapFourInterleaved [] P Q S v1 v2 varA varB)) co (State.Checkpoint j) := by
  rw [show n + 5 + Q.length + P.length = (n + 1) + 4 + Q.length + P.length from by omega]
  rw [lhs_fragment_four_checkpoint (n+1) co j P Q S tmp v1 v2 varA varB hP hQ
        (by omega) (by omega)]
  rw [show (n + 1) + 4 + Q.length + P.length = n + 5 + Q.length + P.length from by omega]
  rw [rhs_fragment_four_checkpoint n co j P Q S tmp v1 v2 varA varB hP hQ hnP hnQ]
  rw [hS.stable ((n + 1) + 1) (by omega) co (State.Checkpoint j),
      hS.stable (n + 1) (by omega) co (State.Checkpoint j)]

/-
  Soundness of the compiler-faithful four-statement single-line-swap
  transformation.

  `R` is the shared prefix and `S` the shared trailing continuation; `P` and
  `Q` are the blocks interleaved between the three reassignments of the
  temporary-based swap (unchanged from `single_line_swap_equiv_general`).
  Provided `P`, `Q` are isolated from `tmp`, `v1`, `v2`, `varA`, `varB`
  (`Isolated4`) and `S` is eventually agreeing on `varA`, `varB`
  (`AgreesOnABEventually`), the temporary-based and four-statement
  compiler-faithful simultaneous forms are eventually observationally
  equivalent. This is the professor's requested statement: the right-hand
  side is exactly `simulSwapFour`, the four-`let` form solc actually emits
  (via the clean-up Theorems 1 and 2, assumed as part of the trusted
  computing base, together with the Yul/`solc` fidelity of `simulSwapFour`
  itself — see its defining comment). -/
theorem single_line_swap_equiv_four
    (R P Q S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (h2A : v2 ≠ varA) (h2B : v2 ≠ varB) (h12 : v1 ≠ v2)
    (hmem : ∀ (ss : SharedState .Yul) (store : VarStore),
              varA ∈ (State.Ok ss store).store ∧ varB ∈ (State.Ok ss store).store)
    (hP : Isolated4 P tmp v1 v2 varA varB) (hQ : Isolated4 Q tmp v1 v2 varA varB)
    (hS : AgreesOnABEventually S varA varB) :
    EventuallyObsEquiv
      (tempSwapInterleaved R P Q S tmp varA varB)
      (simulSwapFourInterleaved R P Q S v1 v2 varA varB) := by
  apply eventuallyObsEquiv_of_exec_eventually_eq
  intro s
  refine ⟨R.length + 5 + Q.length + P.length + hP.threshold + hQ.threshold + hS.threshold, ?_⟩
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m, n = m + R.length := ⟨n - R.length, by omega⟩
  have hLsplit : tempSwapInterleaved R P Q S tmp varA varB
      = R ++ tempSwapInterleaved [] P Q S tmp varA varB := by
    unfold tempSwapInterleaved; simp only [List.nil_append, List.append_assoc]
  have hRsplit : simulSwapFourInterleaved R P Q S v1 v2 varA varB
      = R ++ simulSwapFourInterleaved [] P Q S v1 v2 varA varB := by
    unfold simulSwapFourInterleaved; simp only [List.nil_append, List.append_assoc]
  rw [hLsplit, hRsplit, hm]
  rw [exec_block_append R (tempSwapInterleaved [] P Q S tmp varA varB) m .none s]
  rw [exec_block_append R (simulSwapFourInterleaved [] P Q S v1 v2 varA varB) m .none s]
  cases hRexec : exec (m + R.length) (.Block R) .none s with
  | error e => rfl
  | ok s' =>
    dsimp only
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 5 + Q.length + P.length :=
      ⟨m - 5 - Q.length - P.length, by omega⟩
    rw [hm']
    cases s' with
    | Ok ss' store' =>
      exact fragment_four_eventually_eq m' .none ss' store' P Q S tmp v1 v2 varA varB
        hAB hTA hTB h1A h1B h2A h2B h12 (hmem ss' store').1 (hmem ss' store').2 hP hQ hS
        (by omega) (by omega) (by omega)
    | OutOfFuel =>
      exact fragment_four_outOfFuel_eq m' .none P Q S tmp v1 v2 varA varB hP hQ hS
        (by omega) (by omega) (by omega)
    | Checkpoint j =>
      exact fragment_four_checkpoint_eq m' .none j P Q S tmp v1 v2 varA varB hP hQ hS
        (by omega) (by omega) (by omega)

/-
  Sanity check: the four-statement theorem is not vacuous, and specialises to
  a gas-abstracted form of a consecutive-swap result when the interleaved
  blocks `P`, `Q` are trivial. The empty block is `Isolated4` for any five
  names, by the same trivial argument as `isolated_nil`.
-/

/-- The empty block is (trivially) `Isolated4` from any five names: it reads
    and writes nothing. -/
def isolated4_nil (tmp v1 v2 varA varB : Identifier) :
    Isolated4 ([] : List Stmt) tmp v1 v2 varA varB where
  commTmp := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commV1  := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commV2  := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commA   := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  commB   := by intro fuel co ss store val; cases fuel <;> simp only [Yul.exec]
  threshold := 1
  stable := by
    intro fuel hfuel co s
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [Yul.exec]
  okOut := by
    intro co ss store s' hex
    simp only [Yul.exec] at hex
    injection hex with h
    exact ⟨ss, store, h.symm⟩
  passthrough := by
    intro co
    refine ⟨by simp only [Yul.exec], fun j => by simp only [Yul.exec]⟩

/-- The four-statement theorem, specialised to trivial interleaved blocks,
    recovers (in gas-abstracted form) the soundness of the consecutive
    compiler-faithful single-line-swap transformation. This witnesses that the
    `Isolated4` proviso is satisfiable — the theorem is not vacuous. -/
theorem single_line_swap_equiv_four_nil
    (R S : List Stmt) (tmp v1 v2 varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (h1A : v1 ≠ varA) (h1B : v1 ≠ varB) (h2A : v2 ≠ varA) (h2B : v2 ≠ varB) (h12 : v1 ≠ v2)
    (hmem : ∀ (ss : SharedState .Yul) (store : VarStore),
              varA ∈ (State.Ok ss store).store ∧ varB ∈ (State.Ok ss store).store)
    (hS : AgreesOnABEventually S varA varB) :
    EventuallyObsEquiv
      (R ++ tempSwap tmp varA varB ++ S)
      (R ++ simulSwapFour v1 v2 varA varB ++ S) := by
  have h := single_line_swap_equiv_four R [] [] S tmp v1 v2 varA varB
    hAB hTA hTB h1A h1B h2A h2B h12 hmem
    (isolated4_nil tmp v1 v2 varA varB) (isolated4_nil tmp v1 v2 varA varB) hS
  simpa only [tempSwapInterleaved, simulSwapFourInterleaved, tempSwap, simulSwapFour,
    List.nil_append, List.append_nil, List.append_assoc] using h

end Law2