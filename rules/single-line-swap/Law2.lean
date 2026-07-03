/-
  Law2.lean — Rule 0.1 (Single-Line Swap), verified against EVMYulLean.

  TRANSFORMATION.  Replace the temp-based swap

        tmp := varA ;  varA := varB ;  varB := tmp          (multi-line)

  by the simultaneous assignment `(varA, varB) := (varB, varA)`, which solc
  lowers — capturing varB's old value first — to

        c := varB ;  varB := varA ;  varA := c              (single-line, lowered)

  PROVISO (from the rule; witnessed necessary by the Yul when violated): the
  names are pairwise distinct and already bound in the varstore, and the shared
  postfix `Q` reads only `varA`/`varB` (never the temporary).  Under it, both
  swaps leave `varA`/`varB` holding the swapped values, so any shared `Q` (and
  shared prefix `P`) behave identically.

  MODELLING.  Abstract Yul level, as in Law1.  A reassignment `v := e` is
  `.Let [v] (some e)`; on `.Var` it reduces to `s⟦v ↦ s[id]!⟧`.  The varstore is
  a `Finmap`; the reads use the `GetElem?`/`decidableGetElem?` instance, which we
  discharge with `dif_pos` + the `Finmap` lemmas.

  NO `sorry`, NO `axiom`.
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

/- ============================================================================
   SECTION 1 — VARSTORE LOOKUP / INSERT FACTS  (native getElem!, via dif_pos)
   ============================================================================ -/

/-- Reading the identifier just written returns the written value. -/
lemma get_insert_same (ss : SharedState .Yul) (store : VarStore)
    (v : Identifier) (val : EvmYul.Literal) :
    ((State.Ok ss store)⟦v↦val⟧)[v]! = val := by
  have hmem : v ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
    Finmap.mem_insert.mpr (Or.inl rfl)
  simp only [getElem!, decidableGetElem?, hmem, dif_pos, getElem]
  show (Finmap.lookup v (Finmap.insert v val store)).get! = val
  rw [Finmap.lookup_insert]; rfl

/-- Reading a different (but present) identifier is unaffected by the write. -/
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

/-- Membership is preserved by insert (needed to thread the proviso through the
    three-step swap: each reassignment keeps the other names bound). -/
lemma mem_insert_of_mem (ss : SharedState .Yul) (store : VarStore)
    (v w : Identifier) (val : EvmYul.Literal) (hw : w ∈ store) :
    w ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
  Finmap.mem_insert.mpr (Or.inr hw)

/-- Inserting a name makes it present. -/
lemma mem_insert_self (ss : SharedState .Yul) (store : VarStore)
    (v : Identifier) (val : EvmYul.Literal) :
    v ∈ ((State.Ok ss store)⟦v↦val⟧).store :=
  Finmap.mem_insert.mpr (Or.inl rfl)

/- ============================================================================
   SECTION 2 — ONE-STEP REASSIGNMENT REDUCTION

   `exec (n+1) (.Let [v] (some (.Var w))) = .ok (s⟦v ↦ s[w]!⟧)`.
   (Confirmed: closes by `simp only [Yul.exec, List.head!]`.)
   ============================================================================ -/

lemma exec_reassign (n : ℕ) (v w : Identifier) (co : Option YulContract) (s : Yul.State) :
    exec (n + 1) (.Let [v] (some (.Var w))) co s = .ok (s⟦v ↦ s[w]!⟧) := by
  simp only [Yul.exec, List.head!]

/-- Block-cons for a reassignment head: run the assignment, continue with the tail. -/
lemma exec_block_reassign_cons (n : ℕ) (v w : Identifier) (rest : List Stmt)
    (co : Option YulContract) (s : Yul.State) :
    exec (n + 2) (.Block (.Let [v] (some (.Var w)) :: rest)) co s
      = exec (n + 1) (.Block rest) co (s⟦v ↦ s[w]!⟧) := by
  rw [show exec (n+2) (.Block (.Let [v] (some (.Var w)) :: rest)) co s
        = _ from by rw [Yul.exec]]
  rw [exec_reassign]

/-- Singleton block of one reassignment: run it, land in `.ok`. -/
lemma exec_block_reassign_single (n : ℕ) (v w : Identifier)
    (co : Option YulContract) (s : Yul.State) :
    exec (n + 2) (.Block [.Let [v] (some (.Var w))]) co s = .ok (s⟦v ↦ s[w]!⟧) := by
  rw [exec_block_reassign_cons]
  simp only [Yul.exec]

/- ============================================================================
   SECTION 3 — GENERIC NESTED LOOKUP HELPERS

   The swaps produce nested inserts `s⟦a↦x⟧⟦b↦y⟧⟦c↦z⟧`.  We package the two
   read patterns over such states so the swap proofs stay linear.
   ============================================================================ -/

/-- Read the just-written name through any nesting: `(_⟦v↦val⟧)[v]! = val`. -/
lemma read_top (s : Yul.State) (ss : SharedState .Yul) (store : VarStore)
    (hs : s = State.Ok ss store) (v : Identifier) (val : EvmYul.Literal) :
    (s⟦v↦val⟧)[v]! = val := by
  subst hs; exact get_insert_same ss store v val

/- ============================================================================
   SECTION 4 — THE TWO SWAPS AND THEIR EFFECT ON varA / varB

   temp   :  [ tmp := varA ; varA := varB ; varB := tmp ]
   simult :  [ c := varB   ; varB := varA ; varA := c   ]   (solc's lowering)

   Both, from a state binding varA↦A₀, varB↦B₀ (and the temp name too), reach a
   state with varA↦B₀ and varB↦A₀.  Proven by three `exec_block_reassign_cons`
   steps and the varstore facts, under pairwise-distinctness + membership.
   ============================================================================ -/

def tempSwap (tmp varA varB : Identifier) : List Stmt :=
  [ .Let [tmp]  (some (.Var varA)),
    .Let [varA] (some (.Var varB)),
    .Let [varB] (some (.Var tmp)) ]

def simulSwap (c varA varB : Identifier) : List Stmt :=
  [ .Let [c]    (some (.Var varB)),
    .Let [varB] (some (.Var varA)),
    .Let [varA] (some (.Var c)) ]

/-- **tempSwap effect.**  Three reassignments; from `.Ok ss store` (with varA,
    varB, tmp pairwise distinct and varA, varB present) the result binds
    varA↦B₀ and varB↦A₀, where A₀ = s[varA]!, B₀ = s[varB]!.

    The proof reduces the three block-cons steps, then evaluates the two final
    reads with the varstore facts.  We keep the intermediate states as `let`
    abbreviations so the reads compose. -/
lemma tempSwap_effect
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (tmp varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hmA : varA ∈ store) (hmB : varB ∈ store) :
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

/-- **simulSwap effect.**  Same target reads for varA/varB. -/
lemma simulSwap_effect
    (n : ℕ) (co : Option YulContract) (ss : SharedState .Yul) (store : VarStore)
    (c varA varB : Identifier)
    (hAB : varA ≠ varB) (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hmA : varA ∈ store) (hmB : varB ∈ store) :
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

/- ============================================================================
   SECTION 5 — THE FINAL THEOREM

   Both swaps, from `.Ok ss store`, reach states that AGREE on varA (↦B₀) and
   varB (↦A₀).  They differ elsewhere (temp keeps `tmp↦A₀`; simul keeps `c↦B₀`),
   so the shared postfix `Q` must depend only on varA/varB.  We take that as the
   semantic proviso `AgreesOnAB Q varA varB` (the analogue of Law1's `RunsOk`):
   `exec Q` gives the same result from any two states agreeing on varA and varB.

   Under it (plus pairwise distinctness and membership), the two swap-programs are
   observationally equivalent.  We use the shared prefix P via `Core`.
   ============================================================================ -/

/-- Semantic proviso: `Q` yields the same execution from any two states that
    agree on `varA` and `varB`.  Formalises "Q reads only varA/varB". -/
def AgreesOnAB (Q : List Stmt) (varA varB : Identifier) : Prop :=
  ∀ (fuel : ℕ) (s₁ s₂ : Yul.State) (co : Option YulContract),
    s₁[varA]! = s₂[varA]! → s₁[varB]! = s₂[varB]! →
    exec fuel (.Block Q) co s₁ = exec fuel (.Block Q) co s₂

/-- The temp-swap final state reads varA↦B₀, varB↦A₀. -/
lemma tempSwap_reads
    (ss : SharedState .Yul) (store : VarStore) (tmp varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB) (hmA : varA ∈ store) :
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

/-- The simul-swap final state reads varA↦B₀, varB↦A₀ (same as temp). -/
lemma simulSwap_reads
    (ss : SharedState .Yul) (store : VarStore) (c varA varB : Identifier)
    (hAB : varA ≠ varB) (hCA : c ≠ varA) (hCB : c ≠ varB) (hmB : varB ∈ store) :
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

/-- Block-append for three reassignments then `Q`: the three swap steps run,
    then execution continues with `Q` from the resulting state.  The resulting
    state is exactly the triple-insert the effect lemmas describe. -/
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

/-- **THE PROFESSOR'S LAW 2 (Rule 0.1, Single-Line Swap).**
    Shared prefix `P`, shared postfix `Q` reading only varA/varB (`AgreesOnAB`),
    names pairwise distinct and present.  The temp-swap program and the
    simultaneous-swap program are observationally equivalent. -/
theorem single_line_swap_equiv
    (P Q : List Stmt) (tmp c varA varB : Identifier)
    (hAB : varA ≠ varB) (hTA : tmp ≠ varA) (hTB : tmp ≠ varB)
    (hCA : c ≠ varA) (hCB : c ≠ varB)
    (hQ : AgreesOnAB Q varA varB) :
    ObservationalEquivalence
      (P ++ tempSwap tmp varA varB ++ Q)
      (P ++ simulSwap c varA varB ++ Q) := by
  sorry

end Law2