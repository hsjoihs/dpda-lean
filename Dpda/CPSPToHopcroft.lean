import Dpda.CharPopStringPush
import Dpda.Hopcroft

/--
 - CPSP --> Hopcroft
 -/

def Hopcroft_DPDA_IDesc.fromCPSP {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (pwβ: CPSP_DPDA_IDesc Q S Γ) : Hopcroft_DPDA_IDesc Q S (AugmentZ0 Γ) :=
  ⟨pwβ.p, pwβ.w, pwβ.β.map AugmentZ0.fromΓ ++ [AugmentZ0.z0]⟩

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
      simp [Hopcroft_DPDA_IDesc.fromCPSP, CPSP_Judge.stepTransition, Hopcroft_DPDA.stepTransition, Hopcroft_DPDA.fromCPSP, h]
      match M.transition (idesc.p, AugmentZ0.fromΓ X) with
      | CPSP_Judge.immediate (some (α, p)) =>
        simp [h]
        simp [Hopcroft_DPDA_IDesc.fromCPSP]
      | CPSP_Judge.immediate none =>
        simp [h]
        cases h2 : idesc.w with
        | nil => simp [h2]
        | cons _ _ => simp [h2]
      | CPSP_Judge.step f =>
        simp [h]
        cases h2 : idesc.w with
        | nil => simp [h2]
        | cons a x =>
          simp [h2]
          cases h3 : f a with
          | none =>
            simp [h3]
          | some u =>
            let ⟨k,l⟩ := u
            simp [h3]
            simp [Hopcroft_DPDA_IDesc.fromCPSP]
     | nil =>
      simp [Hopcroft_DPDA_IDesc.fromCPSP, CPSP_Judge.stepTransition, Hopcroft_DPDA.stepTransition, Hopcroft_DPDA.fromCPSP, h]
      match M.transition (idesc.p, AugmentZ0.z0) with
      | CPSP_Judge.immediate (some (α, p)) =>
        simp [h]
        simp [Hopcroft_DPDA_IDesc.fromCPSP]
      | CPSP_Judge.immediate none =>
        simp [h]
        cases h2 : idesc.w with
        | nil => simp [h2]
        | cons _ _ => simp [h2]
      | CPSP_Judge.step f =>
        simp [h]
        cases h2 : idesc.w with
        | nil => simp [h2]
        | cons a x =>
          simp [h2]
          cases h3 : f a with
          | none =>
            simp [h3]
          | some u =>
            let ⟨k,l⟩ := u
            simp [h3]
            simp [Hopcroft_DPDA_IDesc.fromCPSP]

lemma repeat_succ {α} (f : α → α) (n : ℕ) (a : α) :
  Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := by rfl

lemma repeat_lift_map α β γ
  (η_o : α → β)
  (pick: γ → (α → Option α))
  (η_f : γ → (β → Option β))
  (g : γ)
  (th : ∀ a, ((pick g) a).map η_o = (η_f g) (η_o a))
  (n : Nat)
  (a : α) :
  Nat.repeat (lift (η_f g)) n (some (η_o a)) = (Nat.repeat (lift (pick g)) n (some a)).map η_o := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.repeat, lift, ih]
    cases h : Nat.repeat (lift (pick g)) n (some a) with
    | none => rfl
    | some a' =>
      simp [h]
      simp [h] at ih
      rw [← th a']

theorem CPSP_to_Hopcroft_preserves_semantics {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: CPSP_DPDA Q S Γ) (w: List S) (n: ℕ) :
  Hopcroft_DPDA.membership_provable_in_n_steps (Hopcroft_DPDA.fromCPSP M) w n =
  CPSP_DPDA.membership_provable_in_n_steps M w n := by
    let α := CPSP_DPDA_IDesc Q S Γ
    let β := Hopcroft_DPDA_IDesc Q S (AugmentZ0 Γ)
    let γ := CPSP_DPDA Q S Γ
    let η_f : γ → (β → Option β) := fun M => Hopcroft_DPDA.stepTransition (Hopcroft_DPDA.fromCPSP M)
    let th : ∀ idesc, (CPSP_Judge.stepTransition M.transition idesc).map Hopcroft_DPDA_IDesc.fromCPSP = Hopcroft_DPDA.stepTransition (Hopcroft_DPDA.fromCPSP M) (Hopcroft_DPDA_IDesc.fromCPSP idesc) := by
      intro idesc
      exact CPSP_to_Hopcroft_preserves_semantics_single_step M idesc
    let rep :=
      repeat_lift_map α β γ Hopcroft_DPDA_IDesc.fromCPSP (fun M => CPSP_Judge.stepTransition M.transition) η_f M th n ⟨M.q0, w, []⟩
    dsimp only [CPSP_DPDA.membership_provable_in_n_steps, CPSP_DPDA.run_n_steps, Hopcroft_DPDA.membership_provable_in_n_steps, Hopcroft_DPDA.run_n_steps, Hopcroft_DPDA_IDesc.fromCPSP]
    dsimp only [Hopcroft_DPDA_IDesc.fromCPSP] at rep
    rw [show (Hopcroft_DPDA.fromCPSP M).pda.q0 = M.q0 from rfl]
    rw [show [(Hopcroft_DPDA.fromCPSP M).pda.z0] = List.map AugmentZ0.fromΓ [] ++ [AugmentZ0.z0] from rfl]
    rw [rep]
    simp only [Option.map, Hopcroft_DPDA.fromCPSP]
    cases h : Nat.repeat (lift (CPSP_Judge.stepTransition M.transition)) n (some { p := M.q0, w := w, β := [] }) with
    | none => rfl
    | some idesc => rfl
