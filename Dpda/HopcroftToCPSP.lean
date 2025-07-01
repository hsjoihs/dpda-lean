import Dpda.CharPopStringPush
import Dpda.Hopcroft

/--
 - Hopcroft --> CPSP
 -/
def Hopcroft_DPDA_IDesc.toCPSP {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (pwβ: Hopcroft_DPDA_IDesc Q S Γ) : CPSP_DPDA_IDesc (AugmentOneState Q) S Γ :=
  ⟨AugmentOneState.fromQ pwβ.p, pwβ.w, pwβ.β⟩

theorem Hopcroft_to_CPSP_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (idesc: Hopcroft_DPDA_IDesc Q S Γ) :
  let M_cpsp : CPSP_DPDA (AugmentOneState Q) S Γ := Hopcroft_DPDA.toCPSP M
  let idesc_cpsp := Hopcroft_DPDA_IDesc.toCPSP idesc
  let after_step : Option (Hopcroft_DPDA_IDesc Q S Γ) := Hopcroft_DPDA.stepTransition M idesc
  let after_step_cpsp : Option (CPSP_DPDA_IDesc (AugmentOneState Q) S Γ) := CPSP_Judge.stepTransition M_cpsp.transition idesc_cpsp
  after_step.map Hopcroft_DPDA_IDesc.toCPSP = after_step_cpsp := sorry
