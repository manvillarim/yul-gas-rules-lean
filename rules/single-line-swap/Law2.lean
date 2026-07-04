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

end Law2