import Dpda.Basic
import Dpda.WobblyFn
import Dpda.PushOrPop2

universe u_

abbrev PADWTC (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  AugmentZ0 Γ → Option (Q ⊕ (S → Option Q))

def embedPADWTC {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (f: PADWTC Q S Γ) : AugmentZ0 Γ → Option (WobblyFn S Q)
  :=
  fun Γz => match f Γz with
  | none => none
  | some u => WobblyFn.from u

inductive PTPP_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | uncondPush : (Γ × Q) → PTPP_Judge Q S Γ
  | popAndDecideWhetherToConsume : PADWTC Q S Γ → PTPP_Judge Q S Γ

abbrev PTPP_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → PTPP_Judge Q S Γ

structure PTPP_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

structure PTPP_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : PTPP_Transition Q S Γ

def PTPP_Judge.embedInPP {Q: Type u_} {S: Type u_} {Γ: Type u_} (M: PTPP_DPDA Q S Γ)
  : PP2_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | PTPP_Judge.popAndDecideWhetherToConsume f =>
        PP2_Judge.uncondPop fun Γz =>
          (embedPADWTC f Γz : Option (WobblyFn S Q)).map
          (WobblyFn.fmap fun q => ((), q))
      | PTPP_Judge.uncondPush γq =>
        PP2_Judge.observeInput (WobblyFn.noWant (.inl γq))
  }
