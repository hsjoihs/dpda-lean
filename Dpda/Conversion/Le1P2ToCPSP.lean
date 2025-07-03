import Dpda.Definition.CharPopStringPush
import Dpda.Definition.Le1PopLe1Push
import Dpda.Conversion.HopcroftToCPSP
import Dpda.RepeatBindMap

def foo {Q Γ} (G : AugmentZ0 Γ) (wf_Γ : WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q)) : Option (List Γ × Q) :=
  match wf_Γ with
  | WobblyFn.noWant (γe, q) => match G with
    | AugmentZ0.z0 => some (γe.toList, q)
    | AugmentZ0.fromΓ G' => some (γe.toList ++ [G'], q)
  | WobblyFn.want (f : AugmentZ0 Γ → Option (AugmentEpsilon Γ × Q)) =>
    (f G).map fun (γe, q) => (γe.toList, q)

universe u

def trivialEmbedding {Q: Type u} {S: Type u} {Γ: Type u}
  (f : AugmentZ0 Γ → Option (WobblyFn S (AugmentEpsilon Γ × Q))) :
  AugmentZ0 Γ → CPSP_Judge Q S Γ :=
  fun G =>
    let embedded : Option (WobblyFn S (List Γ × Q)) := (f G).map (WobblyFn.fmap fun (γe, q) => (γe.toList, q))
    let split : Option (List Γ × Q) ⊕ (S → Option (List Γ × Q)) := WobblyFn.to_opt embedded
    match split with
    | .inl a => CPSP_Judge.immediate a
    | .inr f => CPSP_Judge.step f

def transposedEmbedding {Q: Type u} {S: Type u} {Γ: Type u}
  (f : WobblyFn S (WobblyFn (AugmentZ0 Γ) (AugmentEpsilon Γ × Q))) :
  AugmentZ0 Γ → CPSP_Judge Q S Γ :=
  fun G =>
    match f with
    | WobblyFn.noWant wfεΓ => CPSP_Judge.immediate (foo G wfεΓ)
    | WobblyFn.want fS_wΓ => CPSP_Judge.step fun S => (fS_wΓ S >>= foo G)

def Le1P2_DPDA.toCPSP {Q S Γ} (M: Le1P2_DPDA Q S Γ) : CPSP_DPDA Q S Γ :=
  let ⟨ q0, F, transition ⟩ := M
  let new_transition_curried : Q → AugmentZ0 Γ → CPSP_Judge Q S Γ
    := fun p =>
      match transition p with
      | Le1P2_Judge.uncondPop f => trivialEmbedding f
      | Le1P2_Judge.observeInput f => transposedEmbedding f
  ⟨ q0, F, fun (q, Γz) =>  new_transition_curried q Γz ⟩

def Le1P2_DPDA_IDesc.toCPSP {Q S Γ} (idesc: Le1P2_DPDA_IDesc Q S Γ) : CPSP_DPDA_IDesc Q S Γ :=
  let ⟨ p, w, β ⟩ := idesc
  ⟨ p, w, β ⟩

def Le1P2_DPDA.run_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Le1P2_DPDA Q S Γ) (w: List S) (n: ℕ) : Option (Le1P2_DPDA_IDesc Q S Γ) :=
  let step : Le1P2_DPDA_IDesc Q S Γ -> Option (Le1P2_DPDA_IDesc Q S Γ) := Le1P2_Judge.stepTransition M.transition
  Nat.repeat (· >>= step) n (some ⟨M.q0, w, []⟩)

def Le1P2_DPDA.membership_provable_in_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Le1P2_DPDA Q S Γ) (w: List S) (n: ℕ) : Bool :=
    match Le1P2_DPDA.run_n_steps M w n with
    | none => false
    | some idesc => (idesc.p ∈ M.F)  && (idesc.w.length == 0)


theorem Le1P2_to_CPSP_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Le1P2_DPDA Q S Γ) (idesc: Le1P2_DPDA_IDesc Q S Γ) :
  let M_cpsp : CPSP_DPDA Q S Γ := Le1P2_DPDA.toCPSP M
  let idesc_cpsp := Le1P2_DPDA_IDesc.toCPSP idesc
  let after_step : Option (Le1P2_DPDA_IDesc Q S Γ) := Le1P2_Judge.stepTransition M.transition idesc
  let after_step_cpsp : Option (CPSP_DPDA_IDesc Q S Γ) := CPSP_Judge.stepTransition M_cpsp.transition idesc_cpsp
  after_step.map Le1P2_DPDA_IDesc.toCPSP = after_step_cpsp := by
    match h2 : M.transition idesc.p with
    | Le1P2_Judge.observeInput wf_S_wΓ =>
      simp [
        Le1P2_Judge.stepTransition, Option.map_none,
        CPSP_Judge.stepTransition,
        Le1P2_DPDA_IDesc.toCPSP,
        lambdaForObserveInput,
        Le1P2_DPDA.toCPSP
      ]
      simp [h2, transposedEmbedding, foo, Option.bind, wobZ, wob]
      match h3 : wf_S_wΓ with
      | WobblyFn.noWant v =>
        simp [h3]
        match h4 : v with
        | WobblyFn.noWant v2 =>
          simp only [List.append_nil, Option.map_some,
            Le1P2_DPDA_IDesc.toCPSP]
          match idesc.β with
          | [] => simp
          | A :: γ => simp
        | WobblyFn.want f2 =>
          simp only
          match h5 : f2 AugmentZ0.z0 with
          | none =>
            simp only [Option.map_none]
            match h6 : idesc.β with
            | [] => simp
            | A :: γ =>
              simp [h6]
              match h7 : f2 (AugmentZ0.fromΓ A) with
              | none =>
                simp only [Option.map_none]
              | some v =>
                simp only [Option.map_some, Le1P2_DPDA_IDesc.toCPSP]
          | some v =>
            simp only [List.append_nil, Option.map_some, Le1P2_DPDA_IDesc.toCPSP]
            match h6 : idesc.β with
            | [] =>
              unfold Le1P2_DPDA_IDesc.toCPSP
              simp
            | A :: γ =>
              simp [h6]
              match h7 : f2 (AugmentZ0.fromΓ A) with
              | none =>
                simp [h7]
              | some v =>
                simp only [Option.map_some, Le1P2_DPDA_IDesc.toCPSP]
      | WobblyFn.want f =>
        simp [h3]
        match h4 : idesc.w with
        | [] =>
          simp [h4, Option.map_none]
          match h6 : idesc.β with
            | [] => rfl
            | _ :: _ => rfl
        | A :: t =>
          simp [h4, Option.map_some]
          match h5 : f A with
          | none =>
            simp [h5, Option.map_none]
            match h6 : idesc.β with
            | [] => rfl
            | _ :: _ => rfl
          | some v =>
            simp [h5, Option.map_some]
            match h6 : v with
            | WobblyFn.noWant v =>
              simp [h6, Le1P2_DPDA_IDesc.toCPSP, foo, lambdaForObserveInput]
              match h6 : idesc.β with
              | _ :: _ => rfl
              | [] => simp
            | WobblyFn.want f =>
              simp [h6, Le1P2_DPDA_IDesc.toCPSP, foo, lambdaForObserveInput]
              match h7 : f AugmentZ0.z0 with
              | none =>
                simp only [Option.map_none]
                match h6 : idesc.β with
                | [] => simp
                | A :: γ =>
                 simp
                 match f (AugmentZ0.fromΓ A) with
                  | none =>
                    simp
                  | some v =>
                    simp [Le1P2_DPDA_IDesc.toCPSP]
              | some y =>
                simp only [lambdaForObserveInput, List.append_nil, Option.map_some,
                  Le1P2_DPDA_IDesc.toCPSP]
                match h6 : idesc.β with
                | [] =>
                  simp [Le1P2_DPDA_IDesc.toCPSP]
                | A :: γ =>
                  simp
                  match f (AugmentZ0.fromΓ A) with
                  | none =>
                    simp
                  | some v =>
                    simp [Le1P2_DPDA_IDesc.toCPSP]
    | Le1P2_Judge.uncondPop f_Γ_wSq =>
      simp [Le1P2_DPDA.toCPSP, Le1P2_DPDA_IDesc.toCPSP,
        CPSP_Judge.stepTransition, h2]
      match h4 : idesc.β with
      | [] =>
        simp [Option.map_none]
        match h3 : trivialEmbedding f_Γ_wSq AugmentZ0.z0 with
        | CPSP_Judge.immediate none =>
          simp [h3]
          unfold Le1P2_Judge.stepTransition
          rw [h2, h4]
          simp [valForUncondPop1]
          intro wf h Γε q u
          unfold wob
          simp [trivialEmbedding, WobblyFn.fmap] at h3
          match h5 : wf with
          | WobblyFn.noWant v =>
            simp [h5]
            intro h6 h7
            simp [h, WobblyFn.fmap] at h3
          | WobblyFn.want f =>
            simp [h5]
            match idesc.w with
            | [] =>
              simp
            | A :: t =>
              simp
              match h6 : f A with
              | none =>
                simp only [reduceCtorEq, not_false_eq_true]
              | some v =>
                simp [h, WobblyFn.fmap] at h3
        | CPSP_Judge.immediate (some (α, q)) =>
          simp [Le1P2_DPDA_IDesc.toCPSP, Le1P2_Judge.stepTransition, h2, h4, valForUncondPop1, Option.bind, wob]
          simp [trivialEmbedding] at h3
          match h6 : f_Γ_wSq AugmentZ0.z0 with
          | none =>
            simp [h6]
            simp [h6] at h3
          | some (WobblyFn.noWant v) =>
            simp [h6, WobblyFn.fmap]
            simp [h6, WobblyFn.fmap] at h3
            exact ⟨ h3.right, h3.left ⟩
          | some (WobblyFn.want f) =>
            simp [h6, WobblyFn.fmap]
            simp [h6, WobblyFn.fmap] at h3
        | CPSP_Judge.step f2 =>
          simp [h3]
          simp [trivialEmbedding, WobblyFn.fmap] at h3
          match h6 : f_Γ_wSq AugmentZ0.z0 with
          | none =>
            rw [h6] at h3
            simp at h3
          | some (WobblyFn.noWant q) =>
            simp [h6, WobblyFn.fmap] at h3
          | some (WobblyFn.want f) =>
            simp [h6, WobblyFn.fmap] at h3
            unfold Le1P2_Judge.stepTransition
            simp [h2, h4, valForUncondPop1, Option.bind, wob, h6]
            match h7 : idesc.w with
            | [] =>
              simp [h7, Option.map_none]
            | A :: t =>
              simp [h7, Option.map_some]
              have h8 := congr_fun h3 A
              rw [← h8]
              match h9 : f A with
              | none =>
                simp [h9, Option.map_none]
              | some u =>
                simp [h9, Option.map_some, Le1P2_DPDA_IDesc.toCPSP]
      | A :: γ =>
        simp [Le1P2_Judge.stepTransition, h2, h4, valForUncondPop2, Option.bind, wob]
        match h3 : f_Γ_wSq (AugmentZ0.fromΓ A) with
        | none =>
          simp [Option.map_none, trivialEmbedding, h3]
        | some (WobblyFn.noWant v) =>
          simp [Option.map_some, WobblyFn.fmap, h3, Le1P2_DPDA_IDesc.toCPSP, trivialEmbedding]
        | some (WobblyFn.want f) =>
          simp [Option.map_some, WobblyFn.fmap, h3, Le1P2_DPDA_IDesc.toCPSP, trivialEmbedding]
          match h5 : idesc.w with
          | [] =>
            simp [h5, Option.map_none]
          | A :: t =>
            simp [h5, Option.map_some]
            match h6 : f A with
              | none =>
                simp
              | some u =>
                simp [Le1P2_DPDA_IDesc.toCPSP]


theorem Le1P2_to_CPSP_preserves_semantics {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Le1P2_DPDA Q S Γ) (w: List S) (n: ℕ) :
  CPSP_DPDA.membership_provable_in_n_steps (Le1P2_DPDA.toCPSP M) w n =
  Le1P2_DPDA.membership_provable_in_n_steps M w n := by
    simp only [CPSP_DPDA.membership_provable_in_n_steps, CPSP_DPDA.run_n_steps, Le1P2_DPDA.membership_provable_in_n_steps, Le1P2_DPDA.run_n_steps]
    let α := (Le1P2_DPDA_IDesc Q S Γ)
    let β := CPSP_DPDA_IDesc Q S Γ
    have h := repeat_bind_map2 α β
      Le1P2_DPDA_IDesc.toCPSP
      (Le1P2_Judge.stepTransition M.transition)
      (CPSP_Judge.stepTransition M.toCPSP.transition)
      (Le1P2_to_CPSP_preserves_semantics_single_step M)
      n
    simp at h
    have ha := h { p := M.toCPSP.q0, w := w, β := [] }
    simp [Le1P2_DPDA_IDesc.toCPSP] at ha
    rw [Option.bind_eq_bind]
    rw [ha]
    simp [Le1P2_DPDA.toCPSP]
    set k := (Nat.repeat (fun x ↦ x.bind (Le1P2_Judge.stepTransition M.transition)) n
        (some { p := M.q0, w := w, β := [] })) with hk
    match hk2 : k with
    | none => simp
    | some idesc =>
      simp
      apply decide_and
      · rw [Le1P2_DPDA_IDesc.toCPSP]
      · rw [Le1P2_DPDA_IDesc.toCPSP]
