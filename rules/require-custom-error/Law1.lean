/-
  Verification of the transformation that replaces a `require(B, M)` statement by
  an explicit guarded revert `if (¬B) { revert E() }`.

  Both program forms compile to a Yul conditional `if iszero(B) { body }` whose
  body encodes the failure and terminates in a `revert`. Two results are
  established. When the two bodies coincide, the forms are observationally
  equivalent at every fuel value. When the bodies differ — as they do for a
  string-encoded `require` message versus a four-byte custom-error selector — the
  forms are eventually observationally equivalent, under the hypothesis that each
  body eventually reverts. The latter hypothesis is discharged, for straight-line
  bodies, from the reusable straight-line elimination principle, without any
  appeal to fuel monotonicity.

  The development contains no uses of `sorry` or `axiom`.
-/

import EvmYul.Yul.Ast
import EvmYul.Yul.Interpreter
import EvmYul.Yul.Exception
import EvmYul.Yul.State
import EvmYul.Yul.StateOps
import EvmYul.Yul.PrimOps
import EvmYul.Semantics
import EvmYul.Operations
import Core

open EvmYul Yul Ast Core

set_option autoImplicit false


namespace Law1

lemma step_REVERT_reverts (s : Yul.State) (a b : UInt256) :
    (step (τ := .Yul) (.REVERT : Operation .Yul) (.none : Option (UInt256 × Nat))) s [a, b] =
    .error (.Revert : Yul.Exception) := by
  show (match Yul.binaryMachineStateOp MachineState.evmRevert s [a, b] with
      | .error (e : Yul.Exception) => (.error e : Except Yul.Exception (Yul.State × Option EvmYul.Literal))
      | .ok _ => .error Yul.Exception.Revert) = .error Yul.Exception.Revert
  simp [Yul.binaryMachineStateOp]


lemma primCall_REVERT_reverts (fuel : ℕ) (s : Yul.State) (a b : UInt256) :
    primCall (fuel + 1) s (.REVERT : Operation .Yul) [a, b] =
    .error (.Revert : Yul.Exception) := by
  unfold primCall; simp
  simp [step_REVERT_reverts s a b]


lemma exec_exprStmtCall_REVERT_same (n : ℕ) (codeOverride : Option YulContract) (s' : Yul.State) (a₁ b₁ a₂ b₂ : UInt256) :
    exec n (.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])) codeOverride s' =
    exec n (.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])) codeOverride s' := by
  induction n with
  | zero => unfold exec; rfl
  | succ n ih =>
    unfold exec; simp
    match n with
    | 0 | 1 | 2 | 3 | 4 =>
      unfold execPrimCall; unfold reverse'; unfold evalArgs; simp
      repeat (unfold evalTail; simp; unfold eval; simp; try (unfold cons'); unfold evalArgs; simp)
    | n+5 =>
      unfold execPrimCall
      have h1 : reverse' (evalArgs (n+5) [.Lit b₁, .Lit a₁] codeOverride s') = .ok (s', [a₁, b₁]) := by
        unfold reverse'; unfold evalArgs; simp
        repeat (unfold evalTail; simp; unfold eval; simp; try (unfold cons'); unfold evalArgs; simp)
      have h2 : reverse' (evalArgs (n+5) [.Lit b₂, .Lit a₂] codeOverride s') = .ok (s', [a₂, b₂]) := by
        unfold reverse'; unfold evalArgs; simp
        repeat (unfold evalTail; simp; unfold eval; simp; try (unfold cons'); unfold evalArgs; simp)
      rw [h1, h2]
      simp
      rw [primCall_REVERT_reverts (n+4) s' a₁ b₁, primCall_REVERT_reverts (n+4) s' a₂ b₂]


lemma exec_revert_block_same (fuel' : ℕ) (codeOverride : Option YulContract) (s' : Yul.State) (a₁ b₁ a₂ b₂ : UInt256) :
    exec fuel' (.Block [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])]) codeOverride s' =
    exec fuel' (.Block [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])]) codeOverride s' := by
  induction fuel' with
  | zero => unfold exec; rfl
  | succ n ih =>
    unfold exec; simp
    rw [exec_exprStmtCall_REVERT_same n codeOverride s' a₁ b₁ a₂ b₂]


lemma exec_block_append_revert_same (P : List Stmt) (fuel' : ℕ)
    (codeOverride : Option YulContract) (s' : Yul.State) (a₁ b₁ a₂ b₂ : UInt256) :
    exec fuel' (.Block (P ++
        [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])])) codeOverride s' =
    exec fuel' (.Block (P ++
        [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])])) codeOverride s' := by
  induction P generalizing fuel' s' with
  | nil =>
    simpa using exec_revert_block_same fuel' codeOverride s' a₁ b₁ a₂ b₂
  | cons p ps ih =>
    cases fuel' with
    | zero => unfold exec; rfl
    | succ n =>
      unfold exec; simp
      match exec n p codeOverride s' with
      | .error e => simp
      | .ok s₁ =>
        simp
        exact ih n s₁


theorem law_local_canonical
    (gas : ℕ) (codeOverride : Option YulContract) (s : Yul.State)
    (cond : Expr) (P : List Stmt) (a₁ b₁ a₂ b₂ : UInt256) (k : List Stmt) :
    exec (gas + 2)
      (.Block (.If cond
        (P ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])]) :: k))
      codeOverride s
      =
    exec (gas + 2)
      (.Block (.If cond
        (P ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])]) :: k))
      codeOverride s :=
  Core.if_local_congr gas codeOverride s cond cond _ _ k
    (fun _ => rfl)
    (fun s' => exec_block_append_revert_same P gas codeOverride s' a₁ b₁ a₂ b₂)


lemma exec_block_if_revert_all_fuel
    (codeOverride : Option YulContract)
    (B : Expr) (enc : List Stmt) (a₁ b₁ a₂ b₂ : UInt256) (k : List Stmt) :
    ∀ fuel s,
    exec fuel
      (.Block (.If (.Call (Sum.inl .ISZERO) [B])
        (enc ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])]) :: k))
      codeOverride s
    =
    exec fuel
      (.Block (.If (.Call (Sum.inl .ISZERO) [B])
        (enc ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])]) :: k))
      codeOverride s := by
  intro fuel s
  match fuel with
  | 0         => unfold exec; rfl
  | 1         => simp only [exec]
  | (m + 2)   => exact law_local_canonical m codeOverride s
                    (.Call (Sum.inl .ISZERO) [B]) enc a₁ b₁ a₂ b₂ k


theorem require_custom_error_observationally_equiv
    (B : Expr) (enc P Q : List Stmt) (a₁ b₁ a₂ b₂ : UInt256) :
    ObservationalEquivalence
      (P ++ [.If (.Call (Sum.inl .ISZERO) [B])
               (enc ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])])] ++ Q)
      (P ++ [.If (.Call (Sum.inl .ISZERO) [B])
               (enc ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])])] ++ Q) := by
  intro fuel s
  apply execTopLevel_of_exec_eq
  simp only [List.append_assoc]
  apply exec_block_prefix_congr P .none
  intro fuel' s'
  simp only [List.singleton_append]
  exact exec_block_if_revert_all_fuel .none B enc a₁ b₁ a₂ b₂ Q fuel' s'


/-
  The case of distinct branch bodies.

  For the specific program forms considered here, the distinct-body case admits a
  self-contained proof whose only hypothesis is that each branch body eventually
  reverts. This hypothesis holds for the bodies actually emitted by the compiler,
  which are straight-line sequences of memory writes followed by a `revert` and
  hence neither loop nor depend on memory contents in order to terminate. Since
  `REVERT` discards its arguments, both bodies reduce to the same payload-free
  exception; the guard is common to both forms, so the branch decision agrees; and
  the complementary branch executes the shared continuation.
-/

/-- A block body eventually reverts if, beyond some fuel threshold and uniformly
    in the entry state, its evaluation yields the payload-free revert exception. -/
def EventuallyReverts (body : List Stmt) : Prop :=
  ∃ N : ℕ, ∀ fuel : ℕ, N ≤ fuel → ∀ s : Yul.State,
    exec fuel (.Block body) .none s = .error (.Revert : Yul.Exception)


/-- Equivalence for distinct branch bodies. Given branch bodies `bodyR` and
    `bodyS`, a common guard `iszero(B)`, and a common continuation `Q`, the two
    programs are eventually observationally equivalent under the hypotheses that
    each body eventually reverts. The proof appeals neither to fuel monotonicity
    nor to any unproven assumption. -/
theorem require_custom_error_eventually_equiv_distinct_grounded
    (B : Expr) (bodyR bodyS Q : List Stmt)
    (hR : EventuallyReverts bodyR) (hS : EventuallyReverts bodyS) :
    EventuallyObsEquiv
      ([.If (.Call (Sum.inl .ISZERO) [B]) bodyR] ++ Q)
      ([.If (.Call (Sum.inl .ISZERO) [B]) bodyS] ++ Q) := by
  obtain ⟨NR, hR⟩ := hR
  obtain ⟨NS, hS⟩ := hS
  intro s
  refine ⟨NR + NS + 2, fun fuel hfuel => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, fuel = m + 2 := ⟨fuel - 2, by omega⟩
  have hmR : NR ≤ m := by omega
  have hmS : NS ≤ m := by omega
  -- The two If-statements agree at fuel m+1, at EVERY post-state s₀ (not just s):
  -- identical guard ⇒ identical branch; taken branch both revert; untaken branch
  -- both yield the same `.ok`.  State-uniform so it threads through the block-cons.
  have hif : ∀ s₀ : Yul.State,
      exec (m + 1) (.If (.Call (Sum.inl .ISZERO) [B]) bodyR) .none s₀
    = exec (m + 1) (.If (.Call (Sum.inl .ISZERO) [B]) bodyS) .none s₀ := by
    intro s₀
    simp only [Yul.exec]
    cases hg : eval m (.Call (Sum.inl .ISZERO) [B]) .none s₀ with
    | error e => rfl
    | ok pr =>
      obtain ⟨s'', cond⟩ := pr
      by_cases hz : cond = ⟨0⟩
      · simp [hz]
      · simp only [hz, ne_eq, not_false_eq_true, ite_true]
        rw [hR m hmR s'', hS m hmS s'']
  -- Thread `hif` through the block-cons using exec_block_prefix_congr with
  -- pre = [.If ...] — but the If differs, so instead reduce the cons by hand:
  -- exec (m+2) (.Block (.If R :: Q)) = match exec (m+1) (.If R) with .ok s₁ => exec (m+1) (.Block Q) s₁
  apply execTopLevel_of_exec_eq
  simp only [List.singleton_append]
  -- reduce ONLY the outer Block-cons (exec (m+1+1)), leaving exec (m+1) (.If ...) intact
  show exec (m + 1 + 1) (.Block (.If (.Call (Sum.inl .ISZERO) [B]) bodyR :: Q)) .none s
     = exec (m + 1 + 1) (.Block (.If (.Call (Sum.inl .ISZERO) [B]) bodyS :: Q)) .none s
  conv_lhs => rw [Yul.exec]
  conv_rhs => rw [Yul.exec]
  rw [hif s]


/-
  Summary of results.

  Three theorems are established. For coincident branch bodies,
  `require_custom_error_observationally_equiv` gives observational equivalence at
  every fuel value, without hypotheses. For distinct bodies,
  `require_custom_error_eventually_equiv_distinct_grounded` gives eventual
  observational equivalence under the hypothesis that each body eventually
  reverts. Finally, `require_custom_error_single_if` states the result for the
  single-conditional form with abstract bodies `R` and `S`, under the
  straight-line hypotheses `RunsOk R` and `RunsOk S`.

  These hypotheses express, in a single condition, that the body evaluates
  successfully rather than reverting, diverging, or transferring control non-
  locally. The lemma `eventuallyReverts_of_runsOk` discharges the eventual-revert
  hypotheses from them by induction on the statement list at a fixed fuel, with no
  appeal to fuel monotonicity.
-/



/-- `exec` on a single `revert(p,q)` reverts at fuel ≥ 6.  Used by the bridge
    lemma `eventuallyReverts_of_runsOk` below: once the straight-line prefix R
    has run to `.ok`, the trailing `revert` fires with the payload-free `.error .Revert`. -/
lemma exec_revert_single (n : ℕ) (codeOverride : Option YulContract) (s' : Yul.State) (p q : UInt256) :
    exec (n + 6) (.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit p, .Lit q])) codeOverride s'
      = .error (.Revert : Yul.Exception) := by
  unfold exec; simp
  unfold execPrimCall
  have h1 : reverse' (evalArgs (n+5) [.Lit q, .Lit p] codeOverride s') = .ok (s', [p, q]) := by
    unfold reverse'; unfold evalArgs; simp
    repeat (unfold evalTail; simp; unfold eval; simp; try (unfold cons'); unfold evalArgs; simp)
  rw [h1]
  simp
  rw [primCall_REVERT_reverts (n+4) s' p q]
  simp [multifill']


/-
  The single-conditional form with abstract bodies.

  The target statement asserts the eventual observational equivalence of

      if iszero(B) { R ++ [revert a₁ b₁] }    and    if iszero(B) { S ++ [revert a₂ b₂] }

  for arbitrary straight-line prefixes `R` and `S`, under the separate hypotheses
  `RunsOk R` and `RunsOk S`. Each hypothesis states that the prefix evaluates
  successfully from every state at sufficiently large fuel, and thus neither
  reverts, diverges, nor transfers control non-locally. Under these hypotheses the
  result holds without fuel monotonicity: the lemma `eventuallyReverts_of_runsOk`
  derives the eventual-revert property of `R ++ [revert]` from `RunsOk R` by
  induction on `R` at a fixed fuel, exploiting that the block-cons reduction
  evaluates head and tail at the same fuel, after which the distinct-body theorem
  concludes.
-/

/-- The terminator lemma: the singleton block `[revert(a, b)]` reverts at any fuel
    at least seven, one level being consumed by the block reduction and six by the
    revert call. This instantiates the hypothesis of the straight-line elimination
    principle. -/
lemma exec_block_revert_reverts (a b : UInt256) :
    ∀ (n : ℕ) (s : Yul.State), n ≥ 7 →
      exec n (.Block [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a, .Lit b])]) .none s
        = .error (.Revert : Yul.Exception) := by
  intro n s hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
  rw [show exec (j+7) (.Block [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a, .Lit b])]) .none s
        = _ from by rw [Yul.exec]]
  rw [exec_revert_single j .none s a b]

/-- If a prefix `R` evaluates successfully, then `R ++ [revert(a, b)]` eventually
    reverts. The straight-line induction is supplied by the elimination principle
    of the foundational module; only the terminator lemma is specific to this
    transformation. -/
theorem eventuallyReverts_of_runsOk
    (R : List Stmt) (a b : UInt256) (hR : RunsOk R) :
    EventuallyReverts
      (R ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a, .Lit b])]) := by
  obtain ⟨N, hN⟩ := hR
  refine ⟨N + R.length + 7, fun fuel hfuel s => ?_⟩
  exact Core.exec_prefix_then_tail (.error .Revert) _
    (exec_block_revert_reverts a b) R fuel s (hN fuel (by omega) s) (by omega)

/-- The single-conditional form with abstract straight-line bodies `R` and `S`,
    under the hypotheses `RunsOk R` and `RunsOk S`, is eventually observationally
    equivalent across the two encodings of the failure branch. -/
theorem require_custom_error_single_if
    (B : Expr) (R S : List Stmt) (a₁ b₁ a₂ b₂ : UInt256)
    (hR : RunsOk R) (hS : RunsOk S) :
    EventuallyObsEquiv
      [ .If (.Call (Sum.inl .ISZERO) [B])
          (R ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])]) ]
      [ .If (.Call (Sum.inl .ISZERO) [B])
          (S ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])]) ] := by
  have hRev := eventuallyReverts_of_runsOk R a₁ b₁ hR
  have hSev := eventuallyReverts_of_runsOk S a₂ b₂ hS
  have := require_custom_error_eventually_equiv_distinct_grounded
            B
            (R ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₁, .Lit b₁])])
            (S ++ [.ExprStmtCall (.Call (Sum.inl (.REVERT : Operation .Yul)) [.Lit a₂, .Lit b₂])])
            [] hRev hSev
  simpa using this


end Law1