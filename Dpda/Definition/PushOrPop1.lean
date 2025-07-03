import Dpda.AugmentSingleton
import Dpda.WobblyFn
import Dpda.Definition.PushOrPop2

universe u_

inductive PP1_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | unconditionalPush : (Γ × Q) → PP1_Judge Q S Γ
  | consumeAndDecideToPushOrPop :
      (S → Option (
        (Γ × Q) ⊕ (AugmentZ0 Γ → Option (Unit × Q))
      ) )
      → PP1_Judge Q S Γ
  | popAndDecideWhetherToConsume :
      (AugmentZ0 Γ → Option (Q ⊕ (S → Option Q)))
      → PP1_Judge Q S Γ

structure PP1_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

abbrev PP1_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → PP1_Judge Q S Γ

structure PP1_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : PP1_Transition Q S Γ
