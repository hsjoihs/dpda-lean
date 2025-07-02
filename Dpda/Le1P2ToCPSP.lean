import Dpda.CharPopStringPush
import Dpda.Le1PopLe1Push

def Le1P2_DPDA.toCPSP {Q S Γ} [DecidableEq Q] [DecidableEq Γ] (M: Le1P2_DPDA Q S Γ) : CPSP_DPDA Q S Γ :=
  let ⟨ q0, F, transition ⟩ := M
  let new_transition_curried : Q → AugmentZ0 Γ → CPSP_Judge Q S Γ
    := fun p =>
      match transition p with
      | Le1P2_Judge.uncondPop
          (f : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q)) ) =>
        /- Trivial embedding -/
        fun G =>
          let embedded : Option (WobblyFn S (List Γ × Q)) := (f G).map (WobblyFn.fmap fun (γe, q) => (γe.toList, q))
          let split : Option (List Γ × Q) ⊕ (S → Option (List Γ × Q)) := WobblyFn.to_opt embedded
          match split with
          | .inl a => CPSP_Judge.immediate a
          | .inr f => CPSP_Judge.step f
      | Le1P2_Judge.observeInput wf_S_wΓ => fun G => sorry
  ⟨ q0, F, fun (q, Γz) =>  new_transition_curried q Γz ⟩
