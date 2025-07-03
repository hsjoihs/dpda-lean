import Dpda.Definition.PushOrPop2
import Dpda.Definition.Le1PopLe1Push

universe u_

def inclusionL_ {Q: Type u_} {Γ: Type u_} (v: (Γ × Q) ⊕ (AugmentZ0 Γ → Option (Unit × Q))) :
  WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q) :=
  match v with
  | .inl (γ, q) => WobblyFn.noWant (AugmentEpsilon.fromΓ γ, q)
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

def PP2_DPDA.embedInLe1P2 {Q S Γ} (M: PP2_DPDA Q S Γ) : Le1P2_DPDA Q S Γ :=
  { q0 := M.q0
  , F := M.F
  , transition := fun q =>
      match M.transition q with
      | PP2_Judge.observeInput wf_S_wΓ =>
        Le1P2_Judge.observeInput (inclusionL wf_S_wΓ)
      | PP2_Judge.uncondPop f_Γ_wSq =>
        Le1P2_Judge.uncondPop (inclusionR f_Γ_wSq) }
