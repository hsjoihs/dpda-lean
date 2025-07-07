import Dpda.Definition.Sipser
import Dpda.Definition.PredeterminedToPushOrPop

universe u_

def Predet_DPDA_IDesc.toSipser {Q S Γ} [DecidableEq Q] (M: Predet_DPDA_IDesc Q S Γ) : Sipser_DPDA_IDesc (AugmentOneState Q) S Γ :=
  let ⟨ p, w, β ⟩ := M
  ⟨ AugmentOneState.fromQ p, w, β ⟩


-- The augmented state is the "death trap" state.
-- Since the only way for a Sipser DPDA to fail in a finite amount of time is to pop the stack when it is empty,
-- we add a "death trap" as the following state:
-- · It does not belong to the acceptance set
-- · It keeps on popping the state without consuming the input
def Predet_DPDA.toSipser {Q S Γ} [DecidableEq Q] (M: Predet_DPDA Q S Γ) : Sipser_DPDA (AugmentOneState Q) S Γ :=
  let ⟨ q0, F, dot_delta ⟩ := M
  let sipser_delta_curried : (AugmentOneState Q) → AugmentEpsilon Γ → AugmentEpsilon S → Option (AugmentOneState Q × AugmentEpsilon Γ) :=
    fun p_ => match p_ with
     | AugmentOneState.qNeg1 => /- death trap -/
        /- Should always pop any stack alphabet, without consuming the input.

                             δ(qNeg1, ε, ε) = none
                   ∀ G : Γ,  δ(qNeg1, ε, G) = some (qNeg1, ε)
          ∀ a : S, ∀ G : Γ,  δ(qNeg1, a, G) = none
          ∀ a : S,           δ(qNeg1, a, ε) = none
         -/
       fun stack_consumption input_consumption => match input_consumption, stack_consumption with
        | AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar _ =>
          -- pop the stack and stay in the death trap state
            some (AugmentOneState.qNeg1, AugmentEpsilon.Epsilon)
        | _, _ => none
          -- we do not want any other path that consumes the input

     | AugmentOneState.fromQ p =>
       match dot_delta p with
        | Predet_Judge.uncondPush (α, q) =>
          -- unconditional push
          -- a non-consuming, non-popping transition that pushes α onto the stack
          /-                 δ(p, ε, ε) = some (q, α)
          ∀ a : S,           δ(p, a, ε) = none
                   ∀ G : Γ,  δ(p, ε, G) = none
          ∀ a : S, ∀ G : Γ,  δ(p, a, G) = none
         -/
         fun stack_consumption input_consumption => match input_consumption, stack_consumption with
          | AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon => some (AugmentOneState.fromQ q, AugmentEpsilon.fromChar α)
          | _, _ => none
        | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>
          /- The function `fΓ_wS : AugmentZ0 Γ → Option (Q ⊕ (S → Option Q))` encodes two pieces of information:
            · When applied to .z0, it corresponds to a non-popping transition.
            · When applied to .fromΓ A, it corresponds to a popping transition.

            We need to carefully unpack this and translate it to the Sipser format.
            The "exactly one" condition in Sipser is so difficult to get right.

            So far we have been sifting through the cases by only looking at `p`, the current state.
            Therefore, for each state `p` that arrived at the current code path
             (`Predet_Judge.popAndDecideWhetherToConsume fΓ_wS`), we need to make sure that

            ∀ a x,
                exactly_one_some
                  (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x))
                  (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon))
                  (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x))
                  (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon))


          -/
          let nonpop : Option (Q ⊕ (S → Option Q)) := fΓ_wS AugmentZ0.z0
          match nonpop with
          | some (Sum.inl q) =>
            -- the non-popping, non-consuming transition is populated
            fun stack_consumption input_consumption => match input_consumption, stack_consumption with
            | AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon => some (AugmentOneState.fromQ q, AugmentEpsilon.Epsilon)
            | _, _ => none
          | some (Sum.inr (f2 : S → Option Q)) =>
            -- the non-popping, consuming transition is populated
            fun stack_consumption => match stack_consumption with
            | AugmentEpsilon.fromChar _ =>
              fun input_consumption => none -- the popping path is definitely not populated

            | AugmentEpsilon.Epsilon =>
              /-

              So far, we have guaranteed

              ∀ a x,
                  (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x)) == none
               ∧  (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x)) == none

              Thus we are left with

              ∀ a,
                exactly_one_some
                  (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon))
                  (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon))

              To satisfy this, we populate
               (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon))
               for each `a` in `S`, and we set
               (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon)) to `none`.
              -/
              fun input_consumption => match input_consumption with
              | AugmentEpsilon.Epsilon => none
              | AugmentEpsilon.fromChar a => match f2 a with
                | some q => some (AugmentOneState.fromQ q, AugmentEpsilon.Epsilon)
                | none =>
                  /-
                    Raises an error in the original machine.
                    Since in Sipser we need to populate this, I implement this as a transition to the death trap state.
                  -/
                  some (AugmentOneState.qNeg1, AugmentEpsilon.Epsilon)
          | none =>
            -- The non-popping is unpopulated
            -- Thus we need to populate the popping transition

            fun stack_consumption => match stack_consumption with
            | AugmentEpsilon.Epsilon =>
              fun input_consumption => none -- the non-popping path is definitely not populated

            | AugmentEpsilon.fromChar x =>
              let pop : Option (Q ⊕ (S → Option Q)) := fΓ_wS (AugmentZ0.fromΓ x)
              /-

              So far, we have guaranteed

              ∀ a,
                    (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.Epsilon)) == none
                  ∧ (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.Epsilon)) == none

              Thus we are now left with

              ∀ a x,
                  exactly_one_some
                    (pda.transition (p, AugmentEpsilon.fromChar a, AugmentEpsilon.fromChar x))
                    (pda.transition (p, AugmentEpsilon.Epsilon, AugmentEpsilon.fromChar x))
              -/
              match pop with
              | some (Sum.inl q) =>
                -- The machine popped the stack, got `x`, and moved to `q`, without consuming the input.
                fun input_consumption => match input_consumption with
                | AugmentEpsilon.fromChar _ => none /- A path of consumption should not exist -/
                | AugmentEpsilon.Epsilon => some (AugmentOneState.fromQ q, AugmentEpsilon.Epsilon)
              | some (Sum.inr (f2 : S → Option Q)) =>
                -- The machine popped the stack, got `x`, and decided to consume the input
                fun input_consumption => match input_consumption with
                | AugmentEpsilon.Epsilon => none /- Epsilon transition should not exist -/
                | AugmentEpsilon.fromChar a => match f2 a with
                  | some q => some (AugmentOneState.fromQ q, AugmentEpsilon.fromChar x)
                  | none =>
                    /-
                      Raises an error in the original machine.
                      Since in Sipser we need to populate this, I implement this as a transition to the death trap state.
                    -/
                    some (AugmentOneState.qNeg1, AugmentEpsilon.Epsilon)
              | none =>
                -- The machine popped the stack, got `x`, and decided to raise an error.
                -- Since in Sipser we need to populate this, I implement this as an epsilon transition to the death trap state.
                fun input_consumption => match input_consumption with
                | AugmentEpsilon.Epsilon => some (AugmentOneState.qNeg1, AugmentEpsilon.Epsilon)
                | AugmentEpsilon.fromChar _ => none /- A path of consumption should not exist -/
  let is_deterministic := by
    intro q a x
    simp only
    suffices h :
      exactly_one_some
        (sipser_delta_curried q (AugmentEpsilon.fromChar x) (AugmentEpsilon.fromChar a))
        (sipser_delta_curried q AugmentEpsilon.Epsilon (AugmentEpsilon.fromChar a))
        (sipser_delta_curried q (AugmentEpsilon.fromChar x) AugmentEpsilon.Epsilon)
        (sipser_delta_curried q AugmentEpsilon.Epsilon AugmentEpsilon.Epsilon) = true from h
    simp only [sipser_delta_curried]
    match q with
    | AugmentOneState.qNeg1 => -- death trap state
      simp only [exactly_one_some]
    | AugmentOneState.fromQ p =>
      match h : dot_delta p with
      | Predet_Judge.uncondPush (α, q2) =>
        simp only [exactly_one_some, h]
      | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>
        simp only [exactly_one_some, h]
        match h2 : fΓ_wS AugmentZ0.z0 with
        | some (Sum.inl q2) =>
          simp only
        | some (Sum.inr f2) =>
          simp only
          match h3 : f2 a with
          | some q => simp only
          | none => simp only
        | none =>
          simp only
          match fΓ_wS (AugmentZ0.fromΓ x) with
          | some (Sum.inl q2) =>
            simp only
          | some (Sum.inr f2) =>
            simp only
            match h3 : f2 a with
            | some q => simp only
            | none => simp only
          | none =>
            simp only
  ⟨
    ⟨
    AugmentOneState.fromQ q0,
    Finset.image AugmentOneState.fromQ F,
    fun (p, input_consumption, stack_consumption) => sipser_delta_curried p stack_consumption input_consumption
    ⟩,
    is_deterministic
  ⟩

theorem Predet_to_Sipser_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S] [Fintype Γ] [DecidableEq Γ]
  (M: Predet_DPDA Q S Γ) (idesc: Predet_DPDA_IDesc Q S Γ) :
  Predet_DPDA_IDesc.toSipser <$> M.stepTransition idesc = M.toSipser.stepTransition idesc.toSipser := by
  simp [Functor.map]
  match h : M.transition idesc.p with
  | Predet_Judge.uncondPush (α, q) =>
    simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
    split
    · next r y heq =>
      simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
      have r_is_old : ∃ p, AugmentOneState.fromQ p = r := by
        simp [h] at heq
        use q
        exact heq.left
      obtain ⟨ r_in_p, r_is_old ⟩ := r_is_old
      use ⟨ r_in_p, idesc.w, y.toList ++ idesc.β ⟩
      simp [r_is_old]
      simp [h] at heq
      obtain ⟨ h_qr, h_αy ⟩ := heq
      unfold Predet_Transition.stepTransition
      simp [h]
      suffices assert : q = r_in_p ∧ α :: idesc.β = y.toList ++ idesc.β from assert
      constructor
      · rw [← r_is_old] at h_qr
        simp at h_qr
        exact h_qr
      · rw [← h_αy]
        simp [AugmentEpsilon.toList]
    · next heq =>
      simp [h] at heq
  | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>
    simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
    split
    · next r y heq =>
      simp [h] at heq
      match h2 : fΓ_wS AugmentZ0.z0 with
      | none => simp [h2] at heq
      | some (Sum.inr f2) => simp [h2] at heq
      | some (Sum.inl q2) =>
        simp [h2] at heq
        obtain ⟨ h_qr, h_εy ⟩ := heq
        simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
        have r_is_old : ∃ p, AugmentOneState.fromQ p = r := by use q2
        obtain ⟨ r_in_p, r_is_old ⟩ := r_is_old
        suffices todo : ∃ a,
            M.transition.stepTransition idesc = some a ∧
            AugmentOneState.fromQ a.p = r ∧
            a.w = idesc.w ∧
            a.β = y.toList ++ idesc.β from todo
        sorry
    · next heq =>
      simp [h] at heq
      match h2 : fΓ_wS AugmentZ0.z0 with
      | some (Sum.inl q2) => simp [h2] at heq
      | none =>
        simp [h2] at heq
        sorry
      | some (Sum.inr f2) =>
        simp [h2] at heq
        match h3 : idesc.w, h4 : idesc.β with
        | [], [] =>
          simp [h3, h4]
          suffices todo : M.transition.stepTransition idesc = none from todo
          sorry
        | [], x :: xs =>
          simp [h3, h4]
          rw [h]
          simp
          rw [h2]
          simp
          suffices todo : M.transition.stepTransition idesc = none from todo
          sorry
        | x :: xs, [] =>
          simp [h3, h4]
          rw [h]
          simp
          rw [h2]
          simp
          match h5 : f2 x with
          | some q =>
            simp [h5]
            suffices todo : ∃ a,
              M.transition.stepTransition idesc = some a ∧
              a.toSipser = {
                p := AugmentOneState.fromQ q,
                w := xs,
                β := AugmentEpsilon.Epsilon.toList
            } from todo
            sorry
          | none =>
            simp [h5]
            suffices todo : ∃ a,
              M.transition.stepTransition idesc = some a ∧
              a.toSipser = {
                p := AugmentOneState.qNeg1,
                w := xs,
                β := AugmentEpsilon.Epsilon.toList
            } from todo
            sorry
        | x :: xs, a :: as =>
          simp [h3, h4]
          split
          · sorry
          · next r y2 hb hc hd =>
            rw [h] at hb; simp at hb
            rw [h2] at hb; simp at hb
            rw [h] at hc; simp at hc
            rw [h2] at hc; simp at hc
            rw [h] at hd; simp at hd
            rw [h2] at hd; simp at hd
            simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
            suffices todo : ∃ a,
              M.transition.stepTransition idesc = some a ∧
              AugmentOneState.fromQ a.p = r ∧
              a.w = x :: xs ∧
              a.β = y2.toList ++ as
              from todo
            sorry
          · next r y hb hc hd =>
            rw [h] at hb; simp at hb
            rw [h2] at hb; simp at hb
            rw [h] at hc; simp at hc
            rw [h2] at hc; simp at hc
            rw [h] at hd; simp at hd
            rw [h2] at hd
            simp only [reduceCtorEq] at hd
          · sorry
          · sorry
          · sorry
          · sorry
          · sorry
