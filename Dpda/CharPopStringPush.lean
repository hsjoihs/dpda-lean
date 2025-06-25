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
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Dpda.Basic

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
  Q × (AugmentZ0 Γ) → CPSP_Judge Q S Γ

def CPSP_Judge.stepTransition {Q S Γ}
  (tilde_delta: CPSP_Transition Q S Γ)
  (pwβ: CPSP_DPDA_IDesc Q S Γ)
  : Option (CPSP_DPDA_IDesc Q S Γ) :=
  match pwβ.β with
  | .nil => match tilde_delta (pwβ.p, .z0) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some (α, q)) => some ⟨q, pwβ.w, α⟩
    | CPSP_Judge.step f => match pwβ.w with
      | .nil => none
      | a :: x => match f a with
        | none => none
        | some (α, q) => some ⟨q, x, α⟩
  | .cons A γ => match tilde_delta (pwβ.p, .fromΓ A) with
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
  Nat.repeat (lift step) n (some ⟨M.q0, w, []⟩)

def CPSP_DPDA.membership_provable_in_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ]
  (M: CPSP_DPDA Q S Γ) (w: List S) (n: ℕ) : Bool :=
    match CPSP_DPDA.run_n_steps M w n with
    | none => false
    | some idesc => (idesc.p ∈ M.F) && (idesc.w.length == 0)
