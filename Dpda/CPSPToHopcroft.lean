import Dpda.CharPopStringPush
import Dpda.Hopcroft
import Dpda.RepeatBindMap

/--
 - CPSP --> Hopcroft
 -/

def Hopcroft_DPDA_IDesc.fromCPSP {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (pwβ: CPSP_DPDA_IDesc Q S Γ) : Hopcroft_DPDA_IDesc Q S (AugmentZ0 Γ) :=
  ⟨pwβ.p, pwβ.w, pwβ.β.map AugmentZ0.fromΓ ++ [AugmentZ0.z0]⟩

def Hopcroft_DPDA.Δ {Q S Γ} (M: Hopcroft_DPDA Q S Γ) : Q × Γ → CPSP_Judge (AugmentOneState Q) S Γ :=
  fun (q, X) =>
    match M.pda.transition (q, none, X) with
    | some (p, α) => CPSP_Judge.immediate (some (α, AugmentOneState.fromQ p))
    | none => CPSP_Judge.step fun a =>
      match M.pda.transition (q, some a, X) with
      | some (p, α) => some (α, AugmentOneState.fromQ p)
      | none => none

def Hopcroft_DPDA.fromCPSP {Q S Γ} (M_tilde: CPSP_DPDA Q S Γ): Hopcroft_DPDA Q S (AugmentZ0 Γ) :=
  let q0 := M_tilde.q0
  let z_0 := AugmentZ0.z0
  let F := M_tilde.F
  let new_transition : Q × Option S × AugmentZ0 Γ → Option (Q × List (AugmentZ0 Γ)) :=
    fun (q, a, X) => match a with
      | none => match M_tilde.transition (q, X) with
        | CPSP_Judge.immediate none => none
        | CPSP_Judge.immediate (some (α, p)) =>
            match X with
            | AugmentZ0.z0 => some (p, (α.map AugmentZ0.fromΓ) ++ [X])
            | _ => some (p, α.map AugmentZ0.fromΓ)
        | CPSP_Judge.step f => none
      | some a => match M_tilde.transition (q, X) with
        | CPSP_Judge.immediate _ => none
        | CPSP_Judge.step f => match f a with
          | none => none
          | some (α, p) =>
             match X with
              | AugmentZ0.z0 => some (p, (α.map AugmentZ0.fromΓ) ++ [X] )
              | _ => some (p, α.map AugmentZ0.fromΓ)
  let pda : Hopcroft_PreDPDA Q S (AugmentZ0 Γ) := ⟨q0, z_0, F, new_transition⟩
  let deterministic : (∀ q X, (∃ a, pda.transition (q, some a, X) ≠ none) → pda.transition (q, none, X) = none) := by
    intros q X h
    rw [show pda.transition = new_transition from rfl]
    dsimp only [new_transition]
    rw [show pda.transition = new_transition from rfl] at h
    dsimp only [new_transition] at h
    rcases h with ⟨a, h⟩
    cases hc : M_tilde.transition (q, X) with
    | immediate _ => rw [hc] at h; contradiction
    | step _ => rw [hc] at h
  ⟨pda, deterministic⟩

theorem CPSP_to_Hopcroft_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: CPSP_DPDA Q S Γ) (idesc: CPSP_DPDA_IDesc Q S Γ) :
  let M_hop := Hopcroft_DPDA.fromCPSP M
  let idesc_hop := Hopcroft_DPDA_IDesc.fromCPSP idesc
  let after_step : Option (CPSP_DPDA_IDesc Q S Γ) := CPSP_Judge.stepTransition M.transition idesc
  let after_step_hop : Option (Hopcroft_DPDA_IDesc Q S (AugmentZ0 Γ)) := Hopcroft_DPDA.stepTransition M_hop idesc_hop
  after_step.map Hopcroft_DPDA_IDesc.fromCPSP = after_step_hop := by
    cases h : idesc.β with
     | cons X β =>
      simp only [
        CPSP_Judge.stepTransition,
        h,
        Hopcroft_DPDA.stepTransition,
        Hopcroft_DPDA_IDesc.fromCPSP,
        Hopcroft_DPDA.fromCPSP,
        List.map_cons, List.cons_append]
      match M.transition (idesc.p, AugmentZ0.fromΓ X) with
      | CPSP_Judge.immediate (some (α, p)) =>
        simp only [Option.map_some, Option.some.injEq]
        simp only [Hopcroft_DPDA_IDesc.fromCPSP, List.map_append, List.append_assoc]
      | CPSP_Judge.immediate none =>
        simp only [Option.map_none]
        cases h2 : idesc.w with
        | nil => simp only
        | cons _ _ => simp only
      | CPSP_Judge.step f =>
        simp only
        cases h2 : idesc.w with
        | nil => simp only [Option.map_none]
        | cons a x =>
          simp only
          cases h3 : f a with
          | none =>
            simp only [Option.map_none]
          | some u =>
            let ⟨k,l⟩ := u
            simp only [Option.map_some, Option.some.injEq]
            simp only [Hopcroft_DPDA_IDesc.fromCPSP, List.map_append, List.append_assoc]
     | nil =>
      simp only [
        CPSP_Judge.stepTransition, h,
        Hopcroft_DPDA.stepTransition,
        Hopcroft_DPDA_IDesc.fromCPSP,
        Hopcroft_DPDA.fromCPSP,
        List.map_nil, List.nil_append, List.append_nil]
      match M.transition (idesc.p, AugmentZ0.z0) with
      | CPSP_Judge.immediate (some (α, p)) =>
        simp only [Option.map_some, Option.some.injEq]
        simp only [Hopcroft_DPDA_IDesc.fromCPSP]
      | CPSP_Judge.immediate none =>
        simp only [Option.map_none]
        cases h2 : idesc.w with
        | nil => simp only
        | cons _ _ => simp only
      | CPSP_Judge.step f =>
        simp only
        cases h2 : idesc.w with
        | nil => simp only [Option.map_none]
        | cons a x =>
          simp only [h2]
          cases h3 : f a with
          | none =>
            simp only [Option.map_none]
          | some u =>
            let ⟨k,l⟩ := u
            simp only [Option.map_some, Option.some.injEq]
            simp only [Hopcroft_DPDA_IDesc.fromCPSP]

theorem CPSP_to_Hopcroft_preserves_semantics {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: CPSP_DPDA Q S Γ) (w: List S) (n: ℕ) :
  Hopcroft_DPDA.membership_provable_in_n_steps (Hopcroft_DPDA.fromCPSP M) w n =
  CPSP_DPDA.membership_provable_in_n_steps M w n := by
    let α := CPSP_DPDA_IDesc Q S Γ
    let β := Hopcroft_DPDA_IDesc Q S (AugmentZ0 Γ)
    let th : ∀ idesc, (CPSP_Judge.stepTransition M.transition idesc).map Hopcroft_DPDA_IDesc.fromCPSP = Hopcroft_DPDA.stepTransition (Hopcroft_DPDA.fromCPSP M) (Hopcroft_DPDA_IDesc.fromCPSP idesc) := by
      intro idesc
      exact CPSP_to_Hopcroft_preserves_semantics_single_step M idesc
    let rep := repeat_bind_map2 α β
      Hopcroft_DPDA_IDesc.fromCPSP
      (CPSP_Judge.stepTransition M.transition)
      (Hopcroft_DPDA.stepTransition (Hopcroft_DPDA.fromCPSP M))
      th
      n
      ⟨M.q0, w, []⟩
    dsimp only [CPSP_DPDA.membership_provable_in_n_steps, CPSP_DPDA.run_n_steps, Hopcroft_DPDA.membership_provable_in_n_steps, Hopcroft_DPDA.run_n_steps, Hopcroft_DPDA_IDesc.fromCPSP]
    dsimp only [Hopcroft_DPDA_IDesc.fromCPSP] at rep
    rw [show (Hopcroft_DPDA.fromCPSP M).pda.q0 = M.q0 from rfl]
    rw [show [(Hopcroft_DPDA.fromCPSP M).pda.z0] = List.map AugmentZ0.fromΓ [] ++ [AugmentZ0.z0] from rfl]
    simp only [Option.bind_eq_bind, List.map_nil, List.nil_append, Option.pure_def, Option.map_eq_map] at rep
    simp only [Option.bind_eq_bind, List.map_nil, List.nil_append]
    rw [rep]
    simp only [Option.map, Hopcroft_DPDA.fromCPSP]
    cases h : Nat.repeat (· >>= (CPSP_Judge.stepTransition M.transition)) n (some { p := M.q0, w := w, β := [] }) with
    | none => rfl
    | some idesc => rfl
