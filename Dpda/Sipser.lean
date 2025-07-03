import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Dpda.AugmentSingleton

structure Sipser_PreDPDA (Q S Γ) where
  q0 : Q
  F : Finset Q
  transition : Q × AugmentEpsilon S × AugmentEpsilon Γ -> Option (Q × AugmentEpsilon Γ)

def exactly_one_some {α}
  (o1 : Option α)
  (o2 : Option α)
  (o3 : Option α)
  (o4 : Option α) := match o1, o2, o3, o4 with
  | some _, none, none, none => true
  | none, some _, none, none => true
  | none, none, some _, none => true
  | none, none, none, some _ => true
  | _, _, _, _ => false

structure Sipser_DPDA(Q S Γ) where
  pda : Sipser_PreDPDA Q S Γ
  deterministic : ∀ q a x,
    exactly_one_some
      (pda.transition (q, a, x))
      (pda.transition (q, a, AugmentEpsilon.Epsilon))
      (pda.transition (q, AugmentEpsilon.Epsilon, x))
      (pda.transition (q, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon))
