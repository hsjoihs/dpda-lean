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

def inclusionL_ {Q: Type u_} {Γ: Type u_} (v: (Γ × Q) ⊕ (AugmentZ0 Γ → Option (Unit × Q))) :
  WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q) :=
  match v with
  | .inl (γ, q) => WobblyFn.noWant (AugmentEpsilon.fromChar γ, q)
  | .inr f =>
    WobblyFn.want fun r =>
     match f r with
      | none => none
      | some ((), q) => some (AugmentEpsilon.Epsilon, q)

def inclusionL {Q: Type u_} {S: Type u_} {Γ: Type u_} (wf_S_wΓ: WobblyFn S ((Γ × Q) ⊕ (AugmentZ0 Γ → Option (Unit × Q)))) :
  WobblyFn S (WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q)) :=
  wf_S_wΓ.fmap inclusionL_

def inclusionR {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (f_Γ_wSq: AugmentZ0 Γ → Option (WobblyFn S (Unit × Q))) :
  AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)) :=
  fun r =>
    match f_Γ_wSq r with
    | none => none
    | some wf_S_wΓ => some (wf_S_wΓ.fmap fun ⟨(), q⟩ => (AugmentEpsilon.Epsilon, q))

def Le1P2_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (hat_delta: Le1P2_Transition Q S Γ)
  (pwβ: Le1P2_DPDA_IDesc Q S Γ)
  : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  match hat_delta pwβ.p with
  | Le1P2_Judge.observeInput wf_S_wΓ =>
    wob wf_S_wΓ pwβ.w >>=
      fun ⟨wfΓ, x⟩ => wobZ wfΓ pwβ.β >>= lambdaForObserveInput x
  | Le1P2_Judge.uncondPop f_Γ_wSq =>
    match pwβ.β with
    | [] => valForUncondPop1 pwβ.w f_Γ_wSq
    | A :: γ => valForUncondPop2 A γ pwβ.w f_Γ_wSq


def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ_: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  let hat_delta : Le1P2_Transition Q S Γ := fun q => match transition q with
    | Predet_Judge.popAndDecideWhetherToConsume f =>
      let f_Γ_wSq := fun Γz =>
        ((match f Γz with
          | none => none
          | some u => WobblyFn.from u) : Option (WobblyFn S Q)).map
        (WobblyFn.fmap fun q => ((), q))
      Le1P2_Judge.uncondPop (inclusionR f_Γ_wSq)
    | Predet_Judge.uncondPush γq =>
      let wf_S_wΓ := (WobblyFn.noWant (.inl γq))
      Le1P2_Judge.observeInput (inclusionL wf_S_wΓ)
  let pwβ : Le1P2_DPDA_IDesc Q S Γ :=
    { p := pwβ_.p
    , w := pwβ_.w
    , β := pwβ_.β }
  let fo : Option (Le1P2_DPDA_IDesc Q S Γ) :=
    match hat_delta pwβ.p with
    | Le1P2_Judge.observeInput wf_S_wΓ =>
      wob wf_S_wΓ pwβ.w >>=
        fun ⟨wfΓ, x⟩ => wobZ wfΓ pwβ.β >>= lambdaForObserveInput x
    | Le1P2_Judge.uncondPop f_Γ_wSq =>
      match pwβ.β with
      | [] => valForUncondPop1 pwβ.w f_Γ_wSq
      | A :: γ => valForUncondPop2 A γ pwβ.w f_Γ_wSq
  fo |>.map fun idesc =>
  { p := idesc.p,
    w := idesc.w,
    β := idesc.β }
