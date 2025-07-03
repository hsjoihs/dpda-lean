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

def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  let fo : Option (Le1P2_DPDA_IDesc Q S Γ) :=
    (
      match transition pwβ.p with
      | Predet_Judge.uncondPush (γ, q) => some ⟨q, pwβ.w, γ :: pwβ.β⟩
      | Predet_Judge.popAndDecideWhetherToConsume f =>
        let f_Γ_wSq' : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)) := (
          fun r =>
            (
              fun a => match a with
              | Sum.inl q => WobblyFn.noWant (AugmentEpsilon.Epsilon, q)
              | Sum.inr f2 =>
                WobblyFn.want fun s =>
                  match f2 s with
                  | none => none
                  | some q => some  (AugmentEpsilon.Epsilon, q)
            ) <$> f r
        )
        match pwβ.β with
          | [] =>
            f_Γ_wSq' AugmentZ0.z0 >>=
              fun wf => (
                match wf with
                | WobblyFn.noWant v => some (v, pwβ.w)
                | WobblyFn.want f => match pwβ.w with
                  | [] => none
                  | A :: t =>
                    match f A with
                    | none => none
                    | some v => some (v, t)
                  ) >>=
                fun ⟨ ⟨ α, q ⟩, x⟩  => some ⟨q, x, α.toList⟩
          | A :: γ =>
              f_Γ_wSq' (AugmentZ0.fromΓ A) >>=
              fun wf => (
                match wf with
                | WobblyFn.noWant v => some (v, pwβ.w)
                | WobblyFn.want f => match pwβ.w with
                  | [] => none
                  | A :: t =>
                    match f A with
                    | none => none
                    | some v => some (v, t)
                  ) >>=
                fun ⟨ ⟨ α, q ⟩, x⟩ => some ⟨q, x, α.toList ++ γ⟩
    )
  fo.map fun idesc =>
  { p := idesc.p,
    w := idesc.w,
    β := idesc.β }
