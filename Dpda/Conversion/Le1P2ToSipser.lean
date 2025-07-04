import Dpda.Definition.Sipser
import Dpda.Definition.Le1PopLe1Push

universe u_

/-

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

-/

-- The augmented state is the "death trap" state.
-- Since the only way for a Sipser DPDA to fail in a finite amount of time is to pop the stack when it is empty,
-- we add a "death trap" as the following state:
-- · It does not belong to the acceptance set
-- · It keeps on popping the state
def Le1P2_DPDA.toSipser {Q S Γ} [DecidableEq Q] (M: Le1P2_DPDA Q S Γ) : Sipser_DPDA (AugmentOneState Q) S Γ :=
  let ⟨ q0, F, hat_delta ⟩ := M
  let sipser_delta : (AugmentOneState Q) × AugmentEpsilon S × AugmentEpsilon Γ → Option (AugmentOneState Q × AugmentEpsilon Γ) :=
    fun (p_, input_consumption, stack_consumption) =>
     match p_ with
     | AugmentOneState.qNeg1 => /- death trap -/
        /- Should always pop any stack alphabet, without consuming the input.

                             δ(qNeg1, ε, ε) = none
                   ∀ G : Γ,  δ(qNeg1, ε, G) = some (qNeg1, ε).
          ∀ a : S, ∀ G : Γ,  δ(qNeg1, a, G) = none
          ∀ a : S,           δ(qNeg1, a, ε) = none
         -/
        match input_consumption, stack_consumption with
        | AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar _ =>
          -- pop the stack and stay in the death trap state
            some (AugmentOneState.qNeg1, AugmentEpsilon.Epsilon)
        | _, _ => none
          -- we do not want any other path that consumes the input

     | AugmentOneState.fromQ p =>
      let new_pwβ : Le1P2_DPDA_IDesc Q S Γ := match hat_delta p with
        | Le1P2_Judge.uncondPop f_Γ_wSq =>
          /- The function `f_Γ_wSq` encodes two pieces of information:
            · When applied to .z0, it corresponds to a non-popping transition.
            · When applied to .fromΓ A, it corresponds to a popping transition.

            We need to carefully unpack this and translate it to the Sipser format.
          -/

          sorry
        | Le1P2_Judge.observeInput wf_S_wΓ => sorry
      sorry
  let is_deterministic := sorry
  ⟨ ⟨ AugmentOneState.fromQ q0, Finset.image AugmentOneState.fromQ F, sipser_delta ⟩, is_deterministic ⟩
