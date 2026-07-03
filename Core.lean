/-
  Core.lean — reusable foundation for verifying Solidity/Yul refactoring laws
  against the EVMYulLean interpreter.

  This module factors out everything from the Law1 proof that is NOT specific to
  the "require → custom error" transformation.  Each law (Law1, the Single-Line
  Swap of Rule 0.1, guard-normalisation laws, etc.) imports `Core` and only has
  to supply its own *core lemma* (the fact that distinguishes its two sides),
  then assembles the top-level theorem from the generic pieces below.

  ─────────────────────────────────────────────────────────────────────────────
  WHAT A NEW LAW REUSES FROM HERE
  ─────────────────────────────────────────────────────────────────────────────
    • Equivalence relations:   ObservationalEquivalence, EventuallyObsEquiv.
    • Top-level bridge:        execTopLevel_of_exec_eq, eventuallyObsEquiv_of_*.
    • Shared context:          exec_block_prefix_congr (shared prefix P),
                               exec_block_postfix via the continuation `k`.
    • Straight-line reasoning: RunsOk, and the induction skeleton used to thread
                               a straight-line prefix that ends in `.ok`.
    • Local `if` congruence for guard-normalisation laws.

  WHAT A NEW LAW MUST SUPPLY
  ─────────────────────────────────────────────────────────────────────────────
    • Its *core lemma*: the single fact that its two local fragments coincide
      (Law1: REVERT discards payload; Rule 0.1: swap-with-temp = simultaneous
      assignment; guard laws: two guards evaluate equally).  Everything else is
      assembled from Core.

  NO `sorry`, NO `axiom` anywhere in this file.
-/

import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.Exception
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Yul.PrimOps
import EvmYul.Semantics
import EvmYul.Operations

open EvmYul Yul Ast

set_option autoImplicit false

namespace Core

/- ============================================================================
   SECTION 1 — EQUIVALENCE RELATIONS

   Two programs (blocks of Yul statements) can be compared at three strengths:
     • ObservationalEquivalence : equal top-level outcome at EVERY fuel.
       Use when the two sides consume identical fuel (e.g. same-length bodies).
     • EventuallyObsEquiv       : equal top-level outcome for all fuel ≥ N.
       Use when the two sides differ in gas cost (e.g. Law1 R ≠ S).
   Both are defined on `execTopLevel`, the observable entry point.
   ============================================================================ -/

/-- Two statement blocks give the same top-level result at every fuel. -/
def ObservationalEquivalence (stmts₁ stmts₂ : List Stmt) : Prop :=
  ∀ (fuel : ℕ) (s : Yul.State),
    execTopLevel fuel (.Block stmts₁) s = execTopLevel fuel (.Block stmts₂) s

/-- Gas-abstracted equivalence: same top-level result once fuel is large enough. -/
def EventuallyObsEquiv (stmts₁ stmts₂ : List Stmt) : Prop :=
  ∀ s : Yul.State, ∃ N, ∀ n, N ≤ n →
    execTopLevel n (.Block stmts₁) s = execTopLevel n (.Block stmts₂) s

/-- `ObservationalEquivalence` is stronger: it implies the eventual form. -/
theorem eventually_of_observational {stmts₁ stmts₂ : List Stmt}
    (h : ObservationalEquivalence stmts₁ stmts₂) :
    EventuallyObsEquiv stmts₁ stmts₂ :=
  fun s => ⟨0, fun n _ => h n s⟩

/- ============================================================================
   SECTION 2 — TOP-LEVEL BRIDGE

   `execTopLevel` is a non-recursive wrapper over `exec`.  These lemmas move an
   equality/eventual-equality obtained at the `exec` level up to the observable
   `execTopLevel` level.  Every law's final theorem passes through here.
   ============================================================================ -/

/-- If two statements give the same `exec` result (no code override), they give
    the same `execTopLevel` result.  The workhorse for all-fuel laws. -/
theorem execTopLevel_of_exec_eq {fuel : ℕ} {stmt₁ stmt₂ : Stmt} {s : Yul.State}
    (h : exec fuel stmt₁ .none s = exec fuel stmt₂ .none s) :
    execTopLevel fuel stmt₁ s = execTopLevel fuel stmt₂ s := by
  unfold execTopLevel; rw [h]

/-- If two blocks eventually give the same `exec` result, they are eventually
    observationally equivalent.  The workhorse for gas-abstracted laws. -/
theorem eventuallyObsEquiv_of_exec_eventually_eq
    (stmts₁ stmts₂ : List Stmt)
    (h : ∀ s, ∃ N, ∀ n, N ≤ n →
          exec n (.Block stmts₁) .none s = exec n (.Block stmts₂) .none s) :
    EventuallyObsEquiv stmts₁ stmts₂ := by
  intro s
  obtain ⟨N, hN⟩ := h s
  refine ⟨N, fun n hn => ?_⟩
  unfold execTopLevel
  rw [hN n hn]

/- ============================================================================
   SECTION 3 — SHARED CONTEXT (PREFIX P AND POSTFIX Q)

   Almost every law has the shape

       P ++ [ local-fragment ] ++ Q         (require/custom, swap, guard, …)

   where P (statements before) and Q (statements after) are IDENTICAL on both
   sides and only the local fragment differs.  These lemmas let a law prove its
   claim about the fragment alone, then lift it through the shared P and Q.

   This is what Rule 0.1 (Single-Line Swap) needs directly: it has shared P and Q
   around the swap fragment.
   ============================================================================ -/

/-- **Shared prefix congruence.**  If two blocks agree (at every fuel and state),
    prepending the SAME prefix `pre` preserves the agreement.
    Induction on `pre`: peel the head, branch on its result. -/
theorem exec_block_prefix_congr (pre : List Stmt) (co : Option YulContract)
    (stmts₁ stmts₂ : List Stmt)
    (h : ∀ fuel s, exec fuel (.Block stmts₁) co s =
                   exec fuel (.Block stmts₂) co s) :
    ∀ fuel s, exec fuel (.Block (pre ++ stmts₁)) co s =
              exec fuel (.Block (pre ++ stmts₂)) co s := by
  intro fuel s
  induction pre generalizing fuel s with
  | nil => simpa using h fuel s
  | cons p ps ih =>
    cases fuel with
    | zero => unfold exec; rfl
    | succ n =>
      unfold exec; simp
      match exec n p co s with
      | .error e => simp
      | .ok s₁   => simp; exact ih n s₁

/- ============================================================================
   SECTION 4 — NAMED ONE-STEP REDUCTIONS OF `exec`

   `exec` reduces one level via `rw [Yul.exec]` (one constructor at a time).
   We deliberately do NOT wrap the block-cons / block-nil reductions as standalone
   lemmas here: Lean generates a fresh match-eliminator for each such statement,
   whose motive does not syntactically match a hand-written `match`, so the
   equality does not close by `rfl`.  Laws that need to reduce a block should call
   `rw [Yul.exec]` (or `simp only [Yul.exec]`) directly at the point of use, where
   the surrounding goal provides the motive.  `exec_block_prefix_congr` (Section 3)
   already packages the common block-cons reasoning in reusable form.
   ============================================================================ -/

/- ============================================================================
   SECTION 5 — STRAIGHT-LINE PREFIX REASONING

   Many laws have a fragment of the form  R ++ [terminator]  where `R` is a
   straight-line block that must run to `.ok` for the terminator to be reached.
   `RunsOk R` packages that proviso; the induction skeleton
   `runsOk_append_elim` threads a straight-line `.ok` prefix through a block-cons
   chain at a length-dependent fuel — WITHOUT fuel-monotonicity.

   Law1 uses this to reach its `revert`; a swap law could use it to reach the
   assignment; etc.
   ============================================================================ -/

/-- Straight-line proviso: beyond a threshold, from any state, running the block
    `R` returns `.ok`.  Encodes "R does not revert, does not loop, does not
    break/continue/leave". -/
def RunsOk (R : List Stmt) : Prop :=
  ∃ N : ℕ, ∀ fuel : ℕ, N ≤ fuel → ∀ s : Yul.State,
    ∃ s', exec fuel (.Block R) .none s = .ok s'

/-- **Straight-line elimination (fixed-fuel induction, NO exec_mono).**
    If the prefix `R` runs to `.ok` at fuel `f` (with `f ≥ R.length + k` for the
    terminator's own fuel need `k`), then executing `R ++ tail` reduces to
    executing `tail` from `R`'s exit state — captured here as: the block
    `R ++ tail` reverts/behaves exactly as `tail` does after `R`.

    We expose the general driver as a hypothesis-parameterised lemma: given that
    the singleton `tail` block yields value `v` from every state at the working
    fuel, and `R` runs to `.ok`, the whole `R ++ tail` yields `v`.

    Concretely a law instantiates `tail` with its terminator (e.g. `[revert]`)
    and `hTail` with the terminator's own reduction lemma. -/
theorem exec_prefix_then_tail
    (v : Except Yul.Exception Yul.State)
    (tail : List Stmt)
    (hTail : ∀ (n : ℕ) (s : Yul.State), n ≥ 7 →
        exec n (.Block tail) .none s = v) :
    ∀ (R : List Stmt) (f : ℕ) (s : Yul.State),
      (∃ s', exec f (.Block R) .none s = .ok s') → f ≥ R.length + 7 →
      exec f (.Block (R ++ tail)) .none s = v := by
  intro R
  induction R with
  | nil =>
    intro f s _ hf
    simp only [List.nil_append]
    exact hTail f s (by simp only [List.length_nil] at hf; omega)
  | cons p ps ih =>
    intro f s hok hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [List.length_cons] at hf; omega⟩
    rw [show exec (g+1) (.Block ((p :: ps) ++ tail)) .none s
          = _ from by rw [List.cons_append, Yul.exec]]
    rw [show exec (g+1) (.Block (p :: ps)) .none s = _ from by rw [Yul.exec]] at hok
    cases hp : exec g p .none s with
    | error e =>
      rw [hp] at hok
      obtain ⟨s', hs'⟩ := hok
      exact absurd hs' (by simp)
    | ok s₁ =>
      rw [hp] at hok
      have hok' : ∃ s', exec g (.Block ps) .none s₁ = .ok s' := hok
      have := ih g s₁ hok' (by simp only [List.length_cons] at hf; omega)
      exact this

/- ============================================================================
   SECTION 6 — LOCAL `if` EQUIVALENCE (guard laws)

   For laws that replace one guarded block by another (Law1's require→custom,
   and any guard-normalisation law such as `iszero(iszero B) ≡ B`, De Morgan,
   `x>0 ≡ x≠0`), this generic lemma reduces the obligation to two local facts:
     • hguard  — the two guards evaluate identically from any state;
     • hbodies — the two bodies are observationally interchangeable.
   ============================================================================ -/

/-- **Generic local `if` equivalence.**  Replacing `if condM { bodyM }` by
    `if condE { bodyE }` before a continuation `k` preserves behaviour when the
    guards evaluate identically and the bodies are interchangeable. -/
theorem if_local_congr
    (gas : ℕ) (co : Option YulContract) (s : Yul.State)
    (condM condE : Expr) (bodyM bodyE k : List Stmt)
    (hguard  : ∀ s', eval gas condM co s' = eval gas condE co s')
    (hbodies : ∀ s', exec gas (.Block bodyM) co s'
                   = exec gas (.Block bodyE) co s') :
    exec (gas + 2) (.Block (.If condM bodyM :: k)) co s
      = exec (gas + 2) (.Block (.If condE bodyE :: k)) co s := by
  show exec (gas + 1 + 1) (.Block (.If condM bodyM :: k)) co s
     = exec (gas + 1 + 1) (.Block (.If condE bodyE :: k)) co s
  simp only [Yul.exec]
  simp [hguard, hbodies]

end Core