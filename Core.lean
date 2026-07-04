/-
  A reusable foundation for the mechanised verification of semantics-preserving
  source-to-source transformations against the EVMYulLean interpreter.

  The module isolates the transformation-independent infrastructure: equivalence
  relations on statement blocks, the bridge from the fuel-indexed evaluator to the
  observable top-level semantics, congruence under a shared statement prefix, and
  a fuel-monotonicity-free induction principle for straight-line prefixes. A
  concrete transformation is verified by importing this module, establishing the
  single semantic fact that distinguishes its two program forms, and composing
  that fact with the generic results developed here.

  The development contains no uses of `sorry` or `axiom`; all results are proved
  in the ambient logic and machine-checked by the Lean 4 kernel.
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

/-
  Equivalence relations on statement blocks.

  Two programs are compared at two strengths, both defined on the observable
  entry point `execTopLevel`. Observational equivalence requires agreement at
  every fuel value and is appropriate when the two program forms consume identical
  fuel. Eventual observational equivalence requires agreement only beyond some
  fuel threshold and accommodates forms whose evaluation costs differ.
-/

/-- Two statement blocks give the same top-level result at every fuel. -/
def ObservationalEquivalence (stmts₁ stmts₂ : List Stmt) : Prop :=
  ∀ (fuel : ℕ) (s : Yul.State),
    execTopLevel fuel (.Block stmts₁) s = execTopLevel fuel (.Block stmts₂) s

/-- Gas-abstracted equivalence: same top-level result once fuel is large enough. -/
def EventuallyObsEquiv (stmts₁ stmts₂ : List Stmt) : Prop :=
  ∀ s : Yul.State, ∃ N, ∀ n, N ≤ n →
    execTopLevel n (.Block stmts₁) s = execTopLevel n (.Block stmts₂) s

/-- Observational equivalence implies its eventual form. -/
theorem eventually_of_observational {stmts₁ stmts₂ : List Stmt}
    (h : ObservationalEquivalence stmts₁ stmts₂) :
    EventuallyObsEquiv stmts₁ stmts₂ :=
  fun s => ⟨0, fun n _ => h n s⟩

/-
  From the evaluator to the observable semantics.

  `execTopLevel` is a non-recursive wrapper over the fuel-indexed evaluator
  `exec`. The following results transport an equality, or an eventual equality,
  established at the level of `exec` up to the observable level of `execTopLevel`.
  Every top-level equivalence theorem factors through them.
-/

/-- If two statements give the same `exec` result (no code override), they give
    the same `execTopLevel` result.  This is the principal tool for equivalences that hold at every fuel value. -/
theorem execTopLevel_of_exec_eq {fuel : ℕ} {stmt₁ stmt₂ : Stmt} {s : Yul.State}
    (h : exec fuel stmt₁ .none s = exec fuel stmt₂ .none s) :
    execTopLevel fuel stmt₁ s = execTopLevel fuel stmt₂ s := by
  unfold execTopLevel; rw [h]

/-- If two blocks eventually give the same `exec` result, they are eventually
    observationally equivalent.  This is the principal tool for equivalences that hold only beyond a fuel threshold. -/
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

/-
  Congruence under a shared context.

  A transformation typically has the shape `P ++ F ++ Q`, where the surrounding
  statements `P` and `Q` are common to both program forms and only the fragment
  `F` differs. The following result establishes that prepending a common prefix
  preserves equality of evaluation, allowing a proof to concern itself with the
  fragment alone and then lift the conclusion through the shared context.
-/

/-- Congruence under a shared prefix. If two blocks agree at every fuel and state,
    then prepending a common prefix preserves that agreement.
    The proof is by induction on the prefix, analysing the result of its head. -/
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

/-
  A remark on single-step reductions of `exec`.

  One level of `exec` is unfolded by rewriting with its defining equation. We do
  not package the block reductions as standalone lemmas: the elaborator generates
  a distinct match-eliminator for each such reduction, whose motive does not
  syntactically coincide with a hand-written pattern match, so the corresponding
  equation does not hold definitionally. Reductions are therefore performed at the
  point of use, where the surrounding goal supplies the motive; the recurring
  block-cons reasoning is already captured by the shared-prefix congruence above.
-/

/-
  Reasoning about straight-line prefixes.

  Several transformations involve a fragment of the form `R ++ tail`, where `R` is
  a straight-line block that must terminate successfully for control to reach the
  terminator. The predicate `RunsOk` captures this hypothesis. The principle below
  threads a successful straight-line prefix through the block-cons structure at a
  fuel bound depending on the prefix length, and in particular avoids any appeal
  to monotonicity of `exec` in the fuel parameter.
-/

/-- The straight-line hypothesis on a block `R`: beyond some fuel threshold, and
    from every state, evaluation of `R` succeeds. This excludes, in a single
    condition, reversion, non-termination, and non-local control transfer. -/
def RunsOk (R : List Stmt) : Prop :=
  ∃ N : ℕ, ∀ fuel : ℕ, N ≤ fuel → ∀ s : Yul.State,
    ∃ s', exec fuel (.Block R) .none s = .ok s'

/-- Elimination principle for a straight-line prefix, by induction on the prefix
    at a fixed fuel and without recourse to fuel monotonicity. Suppose the block
    `tail` evaluates to a fixed result `v` from every state at any sufficiently
    large fuel, and the prefix `R` evaluates successfully. Then `R ++ tail`
    evaluates to `v`, provided the fuel exceeds the length of `R` by the margin
    required by `tail`. A concrete transformation instantiates `tail` with its
    terminator and `hTail` with the terminator's reduction lemma. -/
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

/-
  Congruence of the conditional statement.

  For transformations that replace one guarded block by another — the elimination
  of a `require` in favour of an explicit conditional revert, or a normalisation of
  the guard expression such as the elimination of a double negation — the following
  result reduces the obligation to two local facts: that the two guards evaluate
  identically from every state, and that the two branch bodies are interchangeable.
-/

/-- Congruence for the conditional statement. Replacing `if condM { bodyM }` by
    `if condE { bodyE }` ahead of a continuation `k` preserves evaluation whenever
    the guards evaluate identically and the branch bodies are interchangeable. -/
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