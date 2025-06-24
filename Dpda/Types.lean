/-
I define a character-popping, string-pushing DPDA (or, \underline{1-popping, $n$-pushing DPDA}) $M$ to be a 6-tuple:

$M=(Q\,, \Sigma\,, \Gamma\,, q_0\,, F\,, \tilde{\delta}\,)$ where \begin{itemize}
    \item $Q$ is a finite set of states
    \item $\Sigma$ is a finite set of input symbols
    \item $\Gamma$ is a finite set of stack symbols
    \item $q_0 : Q$ is the start state
    \item $F\,\subseteq Q$, where $F$ is the set of final states
    \item $ \tilde{\delta}$ is a transition function, where \\ $ \tilde{\delta} : Q \times (\Gamma \cup \{ Z_0 \} ) \to ( (\Sigma \nrightarrow \Gamma^* \times Q ) \ \cup \ (\Gamma^* \times Q )\  \cup \{ \text{undefined} \} ) $
\end{itemize}

-/

import Mathlib.Data.Finset.Basic

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-

-- Thank you https://github.com/kory33/kripke-game-analysis
def finsetEquivCharacteristic [Fintype α] [DecidableEq α] : Finset α ≃ (α → Bool) :=
{ toFun := fun s a => decide (a ∈ s),
  invFun := fun f => Finset.univ.filter (fun a => f a = true),
  left_inv := by intro s; simp,
  right_inv := by intro f; simp
}

-- Thank you https://github.com/kory33/kripke-game-analysis
def finsetProdEquivCurriedCharacteristic [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  : Finset (α × β) ≃ (α → β → Bool) :=
  finsetEquivCharacteristic.trans (Equiv.curry _ _ _)
-/

-- Glossary:
-- CPSP = char-pop, string-push
-- IDesc = Instantaneous Description

inductive CPSP_Judge Q S Γ
  | immediate : Option (List Γ × Q) → CPSP_Judge Q S Γ
  | step : (S → Option (List Γ × Q)) → CPSP_Judge Q S Γ

structure CPSP_DPDA_IDesc(Q S Γ) where
  p : Q
  w : List S
  β : List Γ

abbrev CPSP_Transition Q S Γ :=
  Q × (Option Γ /- Z₀ -/) → CPSP_Judge Q S Γ

def CPSP_Judge.stepTransition {Q S Γ}
  (tilde_delta: CPSP_Transition Q S Γ)
  (pwβ: CPSP_DPDA_IDesc Q S Γ)
  : Option (CPSP_DPDA_IDesc Q S Γ) :=
  match pwβ.β with
  | .nil => match tilde_delta (pwβ.p, none) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some (α, q)) => some ⟨q, pwβ.w, α⟩
    | CPSP_Judge.step f => match pwβ.w with
      | .nil => none
      | a :: x => match f a with
        | none => none
        | some (α, q) => some ⟨q, x, α⟩
  | .cons A γ => match tilde_delta (pwβ.p, some A) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some (α, q)) => some ⟨q, pwβ.w, α ++ γ⟩
    | CPSP_Judge.step f => match pwβ.w with
      | .nil => none
      | a :: x => match f a with
        | none => none
        | some (α, q) => some ⟨q, x, α ++ γ⟩

structure CPSP_DPDA (Q S Γ) where
  q0 : Q
  F : Finset Q
  transition : CPSP_Transition Q S Γ

def CPSP_DPDA.run_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ]
  (M: CPSP_DPDA Q S Γ) (w: List S) (n: ℕ) : Option (CPSP_DPDA_IDesc Q S Γ) :=
  let step : CPSP_DPDA_IDesc Q S Γ -> Option (CPSP_DPDA_IDesc Q S Γ) := CPSP_Judge.stepTransition M.transition
  Nat.repeat
    (fun idesc =>
      match idesc with
      | none => none
      | some idesc' => step idesc')
    n
    (some ⟨M.q0, w, []⟩)

def CPSP_DPDA.membership_provable_in_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ]
  (M: CPSP_DPDA Q S Γ) (w: List S) (n: ℕ) : Bool :=
    match CPSP_DPDA.run_n_steps M w n with
    | none => false
    | some idesc => idesc.p ∈ M.F
