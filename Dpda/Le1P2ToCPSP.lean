import Dpda.CharPopStringPush
import Dpda.Le1PopLe1Push

def foo {Q Γ} [DecidableEq Q] [DecidableEq Γ] (G : AugmentZ0 Γ) (wf_Γ : WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q)) : Option (List Γ × Q) :=
  match wf_Γ with
  | WobblyFn.noWant (γe, q) => match G with
    | AugmentZ0.z0 => some (γe.toList, q)
    | AugmentZ0.fromΓ G' => some (γe.toList ++ [G'], q)
  | WobblyFn.want (f : AugmentZ0 Γ → Option (AugmentEpsilon Γ × Q)) =>
    (f G).map fun (γe, q) => (γe.toList, q)

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
      | Le1P2_Judge.observeInput
          (delta_hat_p : WobblyFn S (WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q))) =>
          fun G =>
            match delta_hat_p with
            | WobblyFn.noWant wfεΓ => CPSP_Judge.immediate (foo G wfεΓ)
            | WobblyFn.want fS_wΓ => CPSP_Judge.step fun S => (fS_wΓ S >>= foo G)
  ⟨ q0, F, fun (q, Γz) =>  new_transition_curried q Γz ⟩
