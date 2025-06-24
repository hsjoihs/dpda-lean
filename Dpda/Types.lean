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
-- ID = Instantaneous Description

inductive CPSP_Judge Q S Γ
  | immediate : Option (List Γ × Q) → CPSP_Judge Q S Γ
  | step : S → Option (List Γ × Q) → CPSP_Judge Q S Γ

structure CPSP_DPDA_ID(Q S Γ) where
  p : Q
  w : List S
  β : List Γ

def CPSP_Judge.stepTransition Q S Γ : CPSP_Judge Q S Γ → CPSP_DPDA_ID Q S Γ -> Option (CPSP_DPDA_ID Q S Γ) := sorry

structure CPSP_DPDA (Q S Γ) [Fintype Q] [Fintype S /- Σ -/] [Fintype Γ] where
  q0 : Q
  F : Finset Q
  transition : Q × (Option Γ /- Z₀ -/) → CPSP_Judge Q S Γ
