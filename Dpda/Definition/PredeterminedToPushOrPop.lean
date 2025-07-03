import Dpda.WobblyFn

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
  : Option (Predet_DPDA_IDesc Q S Γ) := match transition pwβ.p with
  | Predet_Judge.uncondPush (γ, q) => some ⟨q, pwβ.w, γ :: pwβ.β⟩
  | Predet_Judge.popAndDecideWhetherToConsume f =>
    match pwβ.β with
    | [] => do
      let k ← f AugmentZ0.z0
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.w)
      | Sum.inr f2 => match pwβ.w with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, []⟩
    | A :: γ => do
      let k ← f (AugmentZ0.fromΓ A)
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.w)
      | Sum.inr f2 => match pwβ.w with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, γ⟩

def Predet_DPDA.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (M: Predet_DPDA Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  Predet_Transition.stepTransition M.transition pwβ
