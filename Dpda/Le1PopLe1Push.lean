import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Dpda.Basic
import Dpda.AugmentSingleton
import Dpda.WobblyFn

universe u_

-- Glossary:
-- Le1P2 = (≤ 1)-pop, (≤ 1)-push
-- IDesc = Instantaneous Description

inductive Le1P2_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | observeInput : WobblyFn S (WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q)) → Le1P2_Judge Q S Γ
  | uncondPop : (AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q))) → Le1P2_Judge Q S Γ

structure Le1P2_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

abbrev Le1P2_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → Le1P2_Judge Q S Γ

structure Le1P2_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
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
