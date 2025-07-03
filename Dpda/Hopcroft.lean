import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Dpda.CharPopStringPush
import Dpda.AugmentSingleton

-- Hopcroft's DPDA definition [Introduction to Automata Theory, Languages, and Computation 3rd edition (page 252)]

structure Hopcroft_PreDPDA (Q S Γ) where
  q0 : Q
  z0 : Γ
  F : Finset Q
  -- criterion #1: $\delta(q,a,X)$ has at most one member for any $q$ in $Q$, $a$ in $\Sigma$ or $a = \varepsilon$, and $X$ in $\Gamma$.
  transition : Q × Option S × Γ -> Option (Q × List Γ)

structure Hopcroft_DPDA(Q S Γ) where
  pda : Hopcroft_PreDPDA Q S Γ
  -- criterion #2: If $\delta(q,a,X)$ is nonempty, for some $a$ in $\Sigma$, then $\delta(q, \varepsilon, X)$ must be empty.
  deterministic : ∀ q X, (∃ a, pda.transition (q, some a, X) ≠ none) → pda.transition (q, none, X) = none

structure Hopcroft_DPDA_IDesc(Q S Γ) where
  p : Q
  w : List S
  β : List Γ

def Hopcroft_DPDA.stepTransition {Q S Γ} [DecidableEq Q] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ)
  (pwβ: Hopcroft_DPDA_IDesc Q S Γ)
  : Option (Hopcroft_DPDA_IDesc Q S Γ) :=
  let transition := M.pda.transition
  -- When δ(q, some a, X) contains (p, α),
  --     (q, aw, Xβ) ⊢ (p, w, α ++ β).
  -- When δ(q, none, X) contains (p, α),
  --     (q, w, Xβ) ⊢ (p, w, α ++ β).
  match pwβ.β with
  | .nil => none /-
    This path is implicitly assumed to be unreachable, but we must nevertheless handle it.
    Hopcroft's model assumes that we can *trust* the machine's designer,
    such that the stack never becomes empty:
    the expectation is that, as a *social norm*, one must replenish Z₀ after consuming Z₀ from the stack. -/
  | X :: β =>
    match transition (pwβ.p, none, X) with
    | some (p, α) =>
      /-
      -- If δ(q, none, X) is nonempty, we can use the epsilon transition.
      -- In particular, thanks to the deterministic condition (criterion #2; M.pda.deterministic),
      -- we know that δ(q, some a, X) is empty for any a in S.
      -- Thus the only option is to use the epsilon transition.

      -- Note that this reasoning does not need to be proven formally; we can simply assume it.
      -- We DO need it in order to prove that Hopcroft's DPDA is a subset of Hopcroft's non-deterministic DPDA.
      -/
      some ⟨p, pwβ.w, α ++ β⟩
    | none =>
      /-
      -- If δ(q, none, X) is empty, we must use the transition that consumes a symbol from the input.
      -/
      match pwβ.w with
      | .nil => none -- cannot consume from an empty input
      | a :: w' => match transition (pwβ.p, some a, X) with
        | some (p, α) => some ⟨p, w', α ++ β⟩
        | none => none

def Hopcroft_DPDA.run_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (w: List S) (n: ℕ) : Option (Hopcroft_DPDA_IDesc Q S Γ) :=
  let step : Hopcroft_DPDA_IDesc Q S Γ -> Option (Hopcroft_DPDA_IDesc Q S Γ) := Hopcroft_DPDA.stepTransition M
  Nat.repeat (· >>= step) n
    (some ⟨M.pda.q0, w, M.pda.z0 :: []⟩)

def Hopcroft_DPDA.membership_provable_in_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (w: List S) (n: ℕ) : Bool :=
    match Hopcroft_DPDA.run_n_steps M w n with
    | none => false
    | some idesc => (idesc.p ∈ M.pda.F)  && (idesc.w.length == 0)
