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
    | AugmentOneState.qNeg1, none =>
      CPSP_Judge.immediate (some
        (M.pda.z0 :: [], AugmentOneState.fromQ M.pda.q0)
      ) -- protect the stack bottom
    | AugmentOneState.qNeg1, some _ => CPSP_Judge.immediate none -- stack shall be empty at the start
    | AugmentOneState.fromQ _, none => CPSP_Judge.immediate none -- stack shall never be empty later
    | AugmentOneState.fromQ q, some x => Hopcroft_DPDA.Δ M ⟨q, x⟩
  ⟨q_neg1, F, new_transition⟩
