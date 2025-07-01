import Dpda.CharPopStringPush
import Dpda.Hopcroft

/--
 - Hopcroft --> CPSP
 -/
def Hopcroft_DPDA_IDesc.toCPSP {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (pwβ: Hopcroft_DPDA_IDesc Q S Γ) : CPSP_DPDA_IDesc (AugmentOneState Q) S Γ :=
  ⟨AugmentOneState.fromQ pwβ.p, pwβ.w, pwβ.β⟩

def Hopcroft_DPDA.toCPSP {Q S Γ} [DecidableEq Q] [DecidableEq Γ] (M: Hopcroft_DPDA Q S Γ) : CPSP_DPDA (AugmentOneState Q) S Γ :=
  let q_neg1 : AugmentOneState Q := AugmentOneState.qNeg1
  let F : Finset (AugmentOneState Q) := Finset.image (fun (q: Q) => AugmentOneState.fromQ q) M.pda.F
  let new_transition : CPSP_Transition (AugmentOneState Q) S Γ := fun ⟨q', X⟩ =>
    match q', X with
    | AugmentOneState.qNeg1, .z0 =>
      CPSP_Judge.immediate (some
        (M.pda.z0 :: [], AugmentOneState.fromQ M.pda.q0)
      ) -- protect the stack bottom
    | AugmentOneState.qNeg1, .fromΓ _ => CPSP_Judge.immediate none -- stack shall be empty at the start
    | AugmentOneState.fromQ _, .z0 => CPSP_Judge.immediate none -- stack shall never be empty later
    | AugmentOneState.fromQ q, .fromΓ x => Hopcroft_DPDA.Δ M ⟨q, x⟩
  ⟨q_neg1, F, new_transition⟩

theorem Hopcroft_to_CPSP_preserves_semantics_if_transition_is_immediate {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (idesc: Hopcroft_DPDA_IDesc Q S Γ)
  (stack_nonempty_and_transition_immediate: ∃ A γ, idesc.β = A :: γ ∧ ∃ a, M.Δ (idesc.p, A) = CPSP_Judge.immediate a) :
  let M_cpsp : CPSP_DPDA (AugmentOneState Q) S Γ := Hopcroft_DPDA.toCPSP M
  let idesc_cpsp := Hopcroft_DPDA_IDesc.toCPSP idesc
  let after_step : Option (Hopcroft_DPDA_IDesc Q S Γ) := Hopcroft_DPDA.stepTransition M idesc
  let after_step_cpsp : Option (CPSP_DPDA_IDesc (AugmentOneState Q) S Γ) := CPSP_Judge.stepTransition M_cpsp.transition idesc_cpsp
  after_step.map Hopcroft_DPDA_IDesc.toCPSP = after_step_cpsp := by
  simp only [
    Hopcroft_DPDA_IDesc.toCPSP,
    Hopcroft_DPDA.toCPSP,
    Hopcroft_DPDA.stepTransition,
    CPSP_Judge.stepTransition
  ]
  cases h : idesc.β with
  | nil => simp /- However, this case is absurd under our assumption -/
  | cons A γ =>
    simp [h]
    cases h2 : M.Δ (idesc.p, A) with
    | step f =>
      obtain ⟨ A2, γ2, h3, ⟨ a, h4⟩  ⟩ := stack_nonempty_and_transition_immediate
      rw [h3] at h
      simp at h
      rw [h.left] at h4
      rw [h4] at h2
      contradiction
    | immediate a =>
      cases h3 : idesc.w with
      | nil =>
        simp [h3]
        unfold Hopcroft_PreDPDA.transition
        match h4 : M.pda.transition (idesc.p, none, A) with
        | some (p, α) =>
          simp [h4]
          unfold Hopcroft_DPDA_IDesc.toCPSP
          simp
          unfold Hopcroft_DPDA.Δ at h2
          match a with
          | none =>
            simp
            simp at h2
            rw [h4] at h2
            simp at h2
          | some (p2, α2) =>
            simp at h2
            rw [h4] at h2
            simp at h2
            obtain ⟨ u, v ⟩ := h2
            simp
            exact ⟨ v, u ⟩
        | none =>
          simp [h4]
          match a with
          | none =>
            simp
          | some (p2, α2) =>
            simp
            unfold Hopcroft_DPDA.Δ at h2
            simp at h2
            rw [h4] at h2
            simp at h2
      | cons head tail =>
        simp [h3]
        match h4 : CPSP_Judge.immediate a with
        | CPSP_Judge.step b2 =>
          simp [h4]
          unfold Hopcroft_PreDPDA.transition
          cases b2 head with
          | none =>
            simp
            match h5 : M.pda.transition (idesc.p, none, A) with
            | some (p, α) =>
              simp [h5]
              contradiction
            | none =>
              simp [h5]
              match h6 : M.pda.transition (idesc.p, some head, A) with
              | none =>
                simp [h6]
              | some (p2, α2) =>
                simp [h6]
                contradiction
          | some u =>
            simp
            match h5 : M.pda.4 (idesc.p, none, A) with
            | none =>
              simp [h5]
              contradiction
            | some (p, α) =>
              contradiction
        | CPSP_Judge.immediate a2 =>
          unfold Hopcroft_DPDA_IDesc.toCPSP
          unfold Hopcroft_DPDA.Δ at h2
          simp at h2
          match h5 : M.pda.transition (idesc.p, none, A) with
          | some (p, α) =>
            simp
            match a2 with
            | some (u, v) =>
              simp [h5]
              rw [h5] at h2
              simp at h2
              unfold Hopcroft_PreDPDA.transition at h5
              simp at h4
              rw [← h2] at h4
              simp at h4
              exact ⟨ h4.right, h4.left ⟩
            | none =>
              simp at h4
              rw [h4] at h2
              rw [h5] at h2
              simp at h2
          | none =>
            simp
            match M.pda.transition (idesc.p, some head, A) with
            | some (p, α) =>
              simp
              rw [← h4, ← h2, h5]
              simp
              match M.pda.transition (idesc.p, some head, A) with
              | some (p2, α2) =>
                simp
                rw [h5] at h2
                simp at h2
              | none =>
                simp
                rw [h5] at h2
                simp at h2
            | none =>
              simp
              rw [← h4, ← h2, h5]
              simp
              match M.pda.transition (idesc.p, some head, A) with
              | some (p2, α2) =>
                simp
                rw [h5] at h2
                simp at h2
              | none =>
                simp

theorem Hopcroft_to_CPSP_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (idesc: Hopcroft_DPDA_IDesc Q S Γ) :
  let M_cpsp : CPSP_DPDA (AugmentOneState Q) S Γ := Hopcroft_DPDA.toCPSP M
  let idesc_cpsp := Hopcroft_DPDA_IDesc.toCPSP idesc
  let after_step : Option (Hopcroft_DPDA_IDesc Q S Γ) := Hopcroft_DPDA.stepTransition M idesc
  let after_step_cpsp : Option (CPSP_DPDA_IDesc (AugmentOneState Q) S Γ) := CPSP_Judge.stepTransition M_cpsp.transition idesc_cpsp
  after_step.map Hopcroft_DPDA_IDesc.toCPSP = after_step_cpsp := by
  cases h : idesc.β with
  | nil =>
    simp [
      Hopcroft_DPDA_IDesc.toCPSP,
      Hopcroft_DPDA.toCPSP,
      Hopcroft_DPDA.stepTransition,
      CPSP_Judge.stepTransition,
      h
    ] /- However, this case is absurd under our assumption -/
  | cons A γ =>
    simp [h]
    cases h2 : M.Δ (idesc.p, A) with
    | immediate a =>
      have hs : (∃ A γ, idesc.β = A :: γ ∧ ∃ a, M.Δ (idesc.p, A) = CPSP_Judge.immediate a) := by
        use A
        use γ
        constructor
        exact h
        use a
      have h3 := Hopcroft_to_CPSP_preserves_semantics_if_transition_is_immediate M idesc hs
      apply h3
    | step f =>
      simp [
        Hopcroft_DPDA_IDesc.toCPSP,
        Hopcroft_DPDA.toCPSP,
        Hopcroft_DPDA.stepTransition,
        CPSP_Judge.stepTransition,
        h
      ]
      simp [h2]
      cases h3 : idesc.w with
      | nil =>
        simp [h3]
        unfold Hopcroft_PreDPDA.transition
        match h4 : M.pda.4 (idesc.p, none, A) with
        | none =>
          simp [h4]
        | some (p, α) =>
          simp [h4]
          unfold Hopcroft_DPDA.Δ at h2
          simp at h2
          rw [h4] at h2
          simp at h2
      | cons head tail =>
        simp [h3]
        match hq : f head with
        | none =>
          simp
          unfold Hopcroft_DPDA.Δ at h2
          match h4 : M.pda.transition (idesc.p, none, A) with
          | some (p, α) =>
            simp [Option.map_some, Option.some.injEq]
            simp at h2
            rw [h4] at h2
            simp at h2
          | none =>
            simp
            match h5 : M.pda.transition (idesc.p, some head, A) with
            | none =>
              simp
            | some (p2, α2) =>
              simp [h5]
              have h6 := M.deterministic
              simp at h2
              rw [h4] at h2
              simp at h2
              sorry -- function equality in the assumption
        | some val =>
          unfold Hopcroft_DPDA_IDesc.toCPSP
          simp
          match h4 : M.pda.transition (idesc.p, none, A) with
          | some (p, α) =>
            simp
            unfold Hopcroft_DPDA.Δ at h2
            simp at h2
            rw [h4] at h2
            simp at h2
          | none =>
            simp
            match h5 : M.pda.transition (idesc.p, some head, A) with
            | some (p2, α2) =>
              simp
              unfold Hopcroft_DPDA.Δ at h2
              simp at h2
              rw [h4] at h2
              simp at h2
              sorry -- function equality in the assumption
            | none =>
              simp
              unfold Hopcroft_DPDA.Δ at h2
              simp at h2
              rw [h4] at h2
              simp at h2
              sorry -- False
