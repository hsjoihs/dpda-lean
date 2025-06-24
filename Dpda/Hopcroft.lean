import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Dpda.CharPopStringPush

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

inductive AugmentOneState Q
  | fromQ : Q → AugmentOneState Q
  | qNeg1 : AugmentOneState Q
deriving DecidableEq

def Hopcroft_DPDA.Δ {Q S Γ} (M: Hopcroft_DPDA Q S Γ) : Q × Γ → CPSP_Judge (AugmentOneState Q) S Γ :=
  fun (q, X) =>
    match M.pda.transition (q, none, X) with
    | some (p, α) => CPSP_Judge.immediate (some (α, AugmentOneState.fromQ p))
    | none => CPSP_Judge.step fun a =>
      match M.pda.transition (q, some a, X) with
      | some (p, α) => some (α, AugmentOneState.fromQ p)
      | none => none

def Hopcroft_DPDA.toCPSP {Q S Γ} [DecidableEq Q] [DecidableEq Γ] (M: Hopcroft_DPDA Q S Γ) : CPSP_DPDA (AugmentOneState Q) S Γ :=
  let q_neg1 : AugmentOneState Q := AugmentOneState.qNeg1
  let F : Finset (AugmentOneState Q) := Finset.image (fun (q: Q) => AugmentOneState.fromQ q) M.pda.F
  let new_transition : CPSP_Transition (AugmentOneState Q) S Γ := fun ⟨q', X⟩ =>
    match q', X with
    | AugmentOneState.qNeg1, .z0 =>
      CPSP_Judge.immediate (some
        (M.pda.z0 :: [], AugmentOneState.fromQ M.pda.q0)
      ) -- protect the stack bottom
    | AugmentOneState.qNeg1, .fromΓ _ => CPSP_Judge.immediate none -- stack shall be empty at the start
    | AugmentOneState.fromQ _, .z0 => CPSP_Judge.immediate none -- stack shall never be empty later
    | AugmentOneState.fromQ q, .fromΓ x => Hopcroft_DPDA.Δ M ⟨q, x⟩
  ⟨q_neg1, F, new_transition⟩

def Hopcroft_DPDA.fromCPSP {Q S Γ} (M_tilde: CPSP_DPDA Q S Γ): Hopcroft_DPDA Q S (AugmentZ0 Γ) :=
  let q0 := M_tilde.q0
  let z_0 := AugmentZ0.z0
  let F := M_tilde.F
  let new_transition : Q × Option S × AugmentZ0 Γ → Option (Q × List (AugmentZ0 Γ)) :=
    fun (q, a, X) => match a with
      | none => match M_tilde.transition (q, X) with
        | CPSP_Judge.immediate none => none
        | CPSP_Judge.immediate (some (α, p)) => some (p, α.map AugmentZ0.fromΓ)
        | CPSP_Judge.step f => none
      | some a => match M_tilde.transition (q, X) with
        | CPSP_Judge.immediate _ => none
        | CPSP_Judge.step f => match f a with
          | none => none
          | some (α, p) => some (p, α.map AugmentZ0.fromΓ)
  let pda : Hopcroft_PreDPDA Q S (AugmentZ0 Γ) := ⟨q0, z_0, F, new_transition⟩
  let deterministic : (∀ q X, (∃ a, pda.transition (q, some a, X) ≠ none) → pda.transition (q, none, X) = none) := by
    intros q X h
    rw [show pda.transition = new_transition from rfl]
    dsimp only [new_transition]
    rw [show pda.transition = new_transition from rfl] at h
    dsimp only [new_transition] at h
    rcases h with ⟨a, h⟩
    cases hc : M_tilde.transition (q, X) with
    | immediate _ => rw [hc] at h; contradiction
    | step _ => rw [hc] at h
  ⟨pda, deterministic⟩

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
