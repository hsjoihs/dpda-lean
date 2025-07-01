import Dpda.Basic
import Dpda.AugmentSingleton
import Dpda.WobblyFn
import Dpda.PushOrPop2

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

def inclusionUnit
 {Q: Type u_} {S: Type u_} {Γ: Type u_}
 (g: AugmentZ0 Γ → Option (Q ⊕ (S → Option Q)))
 : AugmentZ0 Γ → Option (WobblyFn S (Unit × Q)) := fun Γz => match g Γz with
  | none => none
  | some (.inl q) => some (WobblyFn.noWant ((), q))
  | some (.inr f) => some (WobblyFn.want fun s =>
      match f s with
      | none => none
      | some q => some ((), q))

def PP1_DPDA.embedInPP2 {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (M: PP1_DPDA Q S Γ) : PP2_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | PP1_Judge.unconditionalPush γq =>
        PP2_Judge.observeInput (WobblyFn.noWant (.inl γq))
      | PP1_Judge.consumeAndDecideToPushOrPop f =>
        PP2_Judge.observeInput (WobblyFn.want f)
      | PP1_Judge.popAndDecideWhetherToConsume f =>
        PP2_Judge.uncondPop (inclusionUnit f) }
