import Dpda.CharPopStringPush
import Dpda.Hopcroft

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option


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

inductive StackSymbol2 : Type
| A : StackSymbol2
| Z₀ : StackSymbol2
deriving Ord, BEq, DecidableEq, Repr

instance StackSymbol2.fintype : Fintype StackSymbol2 :=
  open StackSymbol2 in ⟨⟨{A, Z₀}, by simp⟩, fun x => by cases x <;> simp⟩

def Hopcroft_PreDPDA_anbn : Hopcroft_PreDPDA (Fin 3) Char_ StackSymbol2 where
  q0 := 0
  z0 := StackSymbol2.Z₀
  F := {2}
  transition := fun (q, u, γ) =>
    match q, u, γ with
    | 0, none, _ => none -- no epsilon transition in state 0
    | 0, some .a, .A => some (0, [StackSymbol2.A, StackSymbol2.A]) -- consume 'a' and push A onto the stack
    | 0, some .b, .A => some (1, []) -- pop A and move to state 1
    | 0, some .a, .Z₀ => some (0, [StackSymbol2.A, StackSymbol2.Z₀]) -- consume 'a' and push A onto the stack
    | 0, some .b, .Z₀ => none -- cannot consume 'b' in state 0 when the stack is empty
    | 1, some .a, .A => none -- cannot consume 'a' in state 1
    | 1, some .b, .A => some (1, []) -- consume 'b' and stay in state 1
    | 1, none, .A => none -- no epsilon transition in state 1 with A on the stack
    | 1, some .a, .Z₀ => none -- cannot consume 'a' in state 1 when the stack is empty
    | 1, some .b, .Z₀ => none -- cannot consume 'b' in state 1 when the stack is empty
    | 1, none, .Z₀ => some (2, [StackSymbol2.Z₀]) -- stack is empty; move to the final state
    | 2, _, _ => none -- final state, no transitions

def Hopcroft_DPDA_anbn : Hopcroft_DPDA (Fin 3) Char_ StackSymbol2 where
  pda := Hopcroft_PreDPDA_anbn
  deterministic := by
    intros q X h
    match q with
    | 0 => simp [Hopcroft_PreDPDA_anbn]
    | 2 => simp [Hopcroft_PreDPDA_anbn]
    | 1 => match X with
     | .A => simp [Hopcroft_PreDPDA_anbn]
     | .Z₀ =>
        rcases h with ⟨char, h⟩
        match char with
        | .a => simp [Hopcroft_PreDPDA_anbn] at h
        | .b => simp [Hopcroft_PreDPDA_anbn] at h

def STEP := 4
def STRING := [Char_.a, Char_.a, Char_.b, Char_.b]

def cpsp := CPSP_DPDA.run_n_steps CPSP_DPDA_anbn STRING STEP
#eval match cpsp with | some ⟨p, _, _⟩ => some p | none => none
#eval match cpsp with | some ⟨_, w, _⟩ => some w | none => none
#eval match cpsp with | some ⟨_, _, β⟩ => some β | none => none

def hop := Hopcroft_DPDA.run_n_steps Hopcroft_DPDA_anbn STRING STEP
#eval match hop with | some ⟨p, _, _⟩ => some p | none => none
#eval match hop with | some ⟨_, w, _⟩ => some w | none => none
#eval match hop with | some ⟨_, _, β⟩ => some β | none => none
