import Dpda.WobblyFn
import Dpda.Definition.Le1PopLe1Push

universe u_

inductive PP2_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | observeInput : WobblyFn S ((Γ × Q) ⊕ (AugmentZ0 Γ → Option (Unit × Q))) → PP2_Judge Q S Γ
  | uncondPop : (AugmentZ0 Γ → Option (WobblyFn S (Unit × Q))) → PP2_Judge Q S Γ

abbrev PP2_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → PP2_Judge Q S Γ

structure PP2_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : PP2_Transition Q S Γ
