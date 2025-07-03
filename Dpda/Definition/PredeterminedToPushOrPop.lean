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

def wobZ {Γ V} (wf : WobblyFn (AugmentZ0 Γ) V) (β : List Γ) : Option (V × List Γ) :=
  match wf with
  | WobblyFn.noWant v => some (v, β)
  | WobblyFn.want f => match β with
    | [] =>  match f AugmentZ0.z0 with
      | none => none
      | some v => some (v, [])
    | A :: γ =>
      match f (AugmentZ0.fromΓ A) with
      | none => none
      | some v => some (v, γ)

-/

def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  let fo : Option (Le1P2_DPDA_IDesc Q S Γ) :=
    (
      match transition pwβ.p with
      | Predet_Judge.uncondPush (γ, q) =>
        let wf : WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q) := WobblyFn.noWant (AugmentEpsilon.fromChar γ, q)
        (
          match wf with
            | WobblyFn.noWant v => some (v, pwβ.β)
            | WobblyFn.want f => match pwβ.β with
              | [] =>  match f AugmentZ0.z0 with
                | none => none
                | some v => some (v, [])
              | A :: γ =>
                match f (AugmentZ0.fromΓ A) with
                | none => none
                | some v => some (v, γ)
        ) >>= lambdaForObserveInput pwβ.w
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
