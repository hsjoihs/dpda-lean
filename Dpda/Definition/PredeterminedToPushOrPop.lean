import Dpda.WobblyFn
import Dpda.Definition.PushOrPop1
import Dpda.Definition.PushOrPop2

universe u_

abbrev PADWTC (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  AugmentZ0 Γ → Option (Q ⊕ (S → Option Q))

inductive Predet_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | uncondPush : (Γ × Q) → Predet_Judge Q S Γ
  | popAndDecideWhetherToConsume : PADWTC Q S Γ → Predet_Judge Q S Γ

abbrev Predet_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → Predet_Judge Q S Γ

structure Predet_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

structure Predet_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : Predet_Transition Q S Γ
