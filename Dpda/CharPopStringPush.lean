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

inductive AugmentZ0 Γ where
  | fromΓ : Γ → AugmentZ0 Γ
  | z0 : AugmentZ0 Γ
deriving DecidableEq

def equiv_fintype {α β} (eqv : α ≃ β) [ft : Fintype α] : Fintype β :=
  { elems := Fintype.elems.map eqv.toEmbedding,
    complete := by intro b; simp only [Finset.mem_map_equiv, ft.complete]
  }

def augmentZ0_option_equiv {Γ} : AugmentZ0 Γ ≃ Option Γ :=
  let toFn : AugmentZ0 Γ → Option Γ
      | AugmentZ0.fromΓ g => some g
      | AugmentZ0.z0 => none
  let backFn : Option Γ → AugmentZ0 Γ
      | none => AugmentZ0.z0
      | some g => AugmentZ0.fromΓ g
  { toFun := toFn, invFun := backFn,
    left_inv := by intro a; cases a <;> rfl,
    right_inv := by intro o; cases o <;> rfl }

instance AugmentZ0.fintype {Γ} [ft : Fintype Γ]: Fintype (AugmentZ0 Γ) := equiv_fintype augmentZ0_option_equiv.symm

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
    | some idesc => (idesc.p ∈ M.F) && (idesc.w.length == 0)


/-- Testcase 1: a^nb^n -/

inductive Char_ : Type
| a : Char_
| b : Char_
deriving Ord, BEq, DecidableEq, Repr

instance Char_.fintype : Fintype Char_ :=
  open Char_  in ⟨⟨{a, b}, by simp⟩, fun x => by cases x <;> simp⟩

inductive StackSymbol : Type
| A : StackSymbol
deriving Ord, BEq, DecidableEq, Repr

instance StackSymbol.fintype : Fintype StackSymbol :=
  open StackSymbol in ⟨⟨{A}, by simp⟩, fun x => by cases x; simp⟩


def CPSP_DPDA_anbn : CPSP_DPDA (Fin 3) Char_ StackSymbol where
  q0 := 0
  F := {2}
  transition := fun (q, γ) =>
    match q, γ with
    | 0, .fromΓ .A => CPSP_Judge.step fun u =>
      match u with
      | Char_.a => some ([StackSymbol.A, StackSymbol.A], 0) -- consume 'a' and push A onto the stack
      | Char_.b => some ([], 1) -- pop A and move to state 1
    | 0, .z0 => CPSP_Judge.step fun u =>
      match u with
      | Char_.a => some ([StackSymbol.A], 0) -- consume 'a' and push A onto the stack
      | Char_.b => none -- cannot consume 'b' in state 0
    | 1, .fromΓ .A => CPSP_Judge.step fun u =>
      match u with
      | Char_.a => none -- cannot consume 'a' in state 1
      | Char_.b => some ([], 1) -- consume 'b' and stay in state 1
    | 1, .z0 => CPSP_Judge.immediate (some ([], 2)) -- stack is empty; move to the final state
    | 2, _ => CPSP_Judge.step fun _ => none

#guard CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b] 3
#guard CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.b] 5
#guard CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a,  Char_.a, Char_.b, Char_.b, Char_.b] 7

#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 0).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 1).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 2).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 3).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 4).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.a, Char_.b, Char_.a] 5).not

#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 0).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 1).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 2).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 3).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 4).not
#guard (CPSP_DPDA.membership_provable_in_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 5).not

-- def foo := CPSP_DPDA.run_n_steps CPSP_DPDA_anbn [Char_.a, Char_.b, Char_.a] 3
-- #eval match foo with | some ⟨p, _, _⟩ => p | none => 42
-- #eval match foo with | some ⟨_, w, _⟩ => w | none => [Char_.a, Char_.a, Char_.a, Char_.a]
-- #eval match foo with | some ⟨_, _, β⟩ => β | none => [StackSymbol.A, StackSymbol.A, StackSymbol.A, StackSymbol.A]
