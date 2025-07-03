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


def valForUncondPop1_ {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (pwβ_w : List S) (f_Γ_wSq' : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)))
  : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  f_Γ_wSq' AugmentZ0.z0 >>=
    fun fwS => wob fwS pwβ_w >>=
      fun ⟨ ⟨ α, q ⟩, x⟩  => some ⟨q, x, α.toList⟩

def valForUncondPop2_ {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (A : Γ) (γ : List Γ) (pwβ_w : List S)
  (f_Γ_wSq' : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)))
  : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  f_Γ_wSq' (AugmentZ0.fromΓ A) >>=
    fun fwS => wob fwS pwβ_w >>=
      fun ⟨ ⟨ α, q ⟩, x⟩  => some ⟨q, x, α.toList ++ γ⟩

/-

def wob {U V} (wf : WobblyFn U V) (s : List U) : Option (V × List U) :=
  match wf with
  | WobblyFn.noWant v => some (v, s)
  | WobblyFn.want f => match s with
    | [] => none
    | A :: t =>
      match f A with
      | none => none
      | some v => some (v, t)

-/

def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  let fo : Option (Le1P2_DPDA_IDesc Q S Γ) :=
    (
      match transition pwβ.p with
      | Predet_Judge.uncondPush γq =>
        let v : WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q) := (inclusionL_ <| Sum.inl γq)
        wobZ v pwβ.β >>= lambdaForObserveInput pwβ.w
      | Predet_Judge.popAndDecideWhetherToConsume f =>
        let f_Γ_wSq' : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)) := (
          fun r =>
            match
            (match f r with
            | none => none
            | some u => WobblyFn.from u).map
               (WobblyFn.fmap fun q => ((), q))
             with
            | none => none
            | some wf_S_wΓ => some (wf_S_wΓ.fmap fun ⟨(), q⟩ => (AugmentEpsilon.Epsilon, q))
        )
        match pwβ.β with
          | [] => valForUncondPop1_ pwβ.w f_Γ_wSq'
          | A :: γ => valForUncondPop2_ A γ pwβ.w f_Γ_wSq'
    )
  fo.map fun idesc =>
  { p := idesc.p,
    w := idesc.w,
    β := idesc.β }
