import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Dpda.Basic

universe u_

-- Glossary:
-- Le1P2 = (≤ 1)-pop, (≤ 1)-push
-- IDesc = Instantaneous Description

inductive WobblyFn (U: Type u_) (V: Type u_) : Type (max u_ u_)
  | want : (U → Option V) → WobblyFn U V
  | noWant : V → WobblyFn U V

-- wobbly consumption
def wob {U: Type u_} {V: Type u_} (wf : WobblyFn U V) (s : List U) : Option (V × List U) :=
  match wf with
  | WobblyFn.noWant v => some (v, s)
  | WobblyFn.want f => match s with
    | [] => none
    | A :: t =>
      match f A with
      | none => none
      | some v => some (v, t)

-- wobbly consumption, with the semantics that an empty stack always produces a Z0 when popped
def wobZ {Γ: Type u_} {V: Type u_} (wf : WobblyFn (AugmentZ0 Γ) V) (β : List Γ) : Option (V × List Γ) :=
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

inductive Le1P2_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_) : Type (max (max u_ u_) u_)
  | observeInput : WobblyFn S (WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q)) → Le1P2_Judge Q S Γ
  | uncondPop : (AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q))) → Le1P2_Judge Q S Γ

structure Le1P2_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) : Type (max (max u_ u_) u_) where
  p : Q
  w : List S
  β : List Γ

abbrev Le1P2_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) : Type (max (max u_ u_) u_) :=
  Q → Le1P2_Judge Q S Γ

structure Le1P2_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) : Type (max (max u_ u_) u_) where
  q0 : Q
  F : Finset Q
  transition : Le1P2_Transition Q S Γ

def lambdaForObserveInput {Q: Type u_} {S: Type u_} {Γ: Type u_} (x : List S) : (AugmentEpsilon Γ × Q) × List Γ → Option (Le1P2_DPDA_IDesc Q S Γ)
 := fun ⟨(α, q), γ⟩ => some ⟨q, x, α.toList ++ γ⟩

def valForUncondPop1 {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (w : List S) (f_Γ_wSq : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)))
  : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  f_Γ_wSq AugmentZ0.z0 >>=
    fun fwS => wob fwS w >>=
      fun ⟨ ⟨ α, q ⟩, x⟩  => some ⟨q, x, α.toList⟩

def valForUncondPop2 {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (A : Γ) (γ : List Γ) (w : List S)
  (f_Γ_wSq : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)))
  : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  f_Γ_wSq (AugmentZ0.fromΓ A) >>=
    fun fwS => wob fwS w >>=
      fun ⟨ ⟨ α, q ⟩, x⟩  => some ⟨q, x, α.toList ++ γ⟩

def Le1P2_Judge.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
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
