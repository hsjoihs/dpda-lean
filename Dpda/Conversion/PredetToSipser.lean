import Dpda.Definition.Sipser
import Dpda.Definition.PredeterminedToPushOrPop

universe u_

def Predet_DPDA_IDesc.toSipser {Q S Γ} [DecidableEq Q] (M: Predet_DPDA_IDesc Q S Γ) : Sipser_DPDA_IDesc (Option Q) S Γ :=
  let ⟨ p, w, β ⟩ := M
  ⟨ some p, w, β ⟩


-- The augmented state is the "death trap" state.
-- Since the only way for a Sipser DPDA to fail in a finite amount of time is to pop the stack when it is empty,
-- we add a "death trap" as the following state:
-- · It does not belong to the acceptance set
-- · It keeps on popping the state without consuming the input
def Predet_DPDA.toSipser {Q S Γ} [DecidableEq Q] (M: Predet_DPDA Q S Γ) : Sipser_DPDA (Option Q) S Γ :=
  let ⟨ q0, F, dot_delta ⟩ := M
  let sipser_delta_curried : (Option Q) → Option Γ → Option S → Option (Option Q × Option Γ) :=
    fun p_ => match p_ with
     | none => /- death trap -/
        /- Should always pop any stack alphabet, without consuming the input.

                             δ(qNeg1, ε, ε) = none
                   ∀ G : Γ,  δ(qNeg1, ε, G) = some (qNeg1, ε)
          ∀ a : S, ∀ G : Γ,  δ(qNeg1, a, G) = none
          ∀ a : S,           δ(qNeg1, a, ε) = none
         -/
       fun stack_consumption input_consumption => match input_consumption, stack_consumption with
        | none, some _ =>
          -- pop the stack and stay in the death trap state
            some (none, none)
        | _, _ => none
          -- we do not want any other path that consumes the input

     | some p =>
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
          | none, none => some (some q, some α)
          | _, _ => none
        | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>
          /- The function `fΓ_wS : Option Γ → Option (Q ⊕ (S → Option Q))` encodes two pieces of information:
            · When applied to .z0, it corresponds to a non-popping transition.
            · When applied to .fromΓ A, it corresponds to a popping transition.

            We need to carefully unpack this and translate it to the Sipser format.
            The "exactly one" condition in Sipser is so difficult to get right.

            So far we have been sifting through the cases by only looking at `p`, the current state.
            Therefore, for each state `p` that arrived at the current code path
             (`Predet_Judge.popAndDecideWhetherToConsume fΓ_wS`), we need to make sure that

            ∀ a x,
                exactly_one_some
                  (pda.transition (p, some a, some x))
                  (pda.transition (p, some a, none))
                  (pda.transition (p, none, some x))
                  (pda.transition (p, none, none))


          -/
          let nonpop : Option (Q ⊕ (S → Option Q)) := fΓ_wS none
          match nonpop with
          | some (Sum.inl q) =>
            -- the non-popping, non-consuming transition is populated
            fun stack_consumption input_consumption => match input_consumption, stack_consumption with
            | none, none => some (some q, none)
            | _, _ => none
          | some (Sum.inr (f2 : S → Option Q)) =>
            -- the non-popping, consuming transition is populated
            fun stack_consumption => match stack_consumption with
            | some _ =>
              fun input_consumption => none -- the popping path is definitely not populated

            | none =>
              /-

              So far, we have guaranteed

              ∀ a x,
                  (pda.transition (p, some a, some x)) == none
               ∧  (pda.transition (p, none, some x)) == none

              Thus we are left with

              ∀ a,
                exactly_one_some
                  (pda.transition (p, some a, none))
                  (pda.transition (p, none, none))

              To satisfy this, we populate
               (pda.transition (p, some a, none))
               for each `a` in `S`, and we set
               (pda.transition (p, none, none)) to `none`.
              -/
              fun input_consumption => match input_consumption with
              | none => none
              | some a => match f2 a with
                | some q => some (some q, none)
                | none =>
                  /-
                    Raises an error in the original machine.
                    Since in Sipser we need to populate this, I implement this as a transition to the death trap state.
                  -/
                  some (none, none)
          | none =>
            -- The non-popping is unpopulated
            -- Thus we need to populate the popping transition

            fun stack_consumption => match stack_consumption with
            | none =>
              fun input_consumption => none -- the non-popping path is definitely not populated

            | some x =>
              let pop : Option (Q ⊕ (S → Option Q)) := fΓ_wS (some x)
              /-

              So far, we have guaranteed

              ∀ a,
                    (pda.transition (p, some a, none)) == none
                  ∧ (pda.transition (p, none, none)) == none

              Thus we are now left with

              ∀ a x,
                  exactly_one_some
                    (pda.transition (p, some a, some x))
                    (pda.transition (p, none, some x))
              -/
              match pop with
              | some (Sum.inl q) =>
                -- The machine popped the stack, got `x`, and moved to `q`, without consuming the input.
                fun input_consumption => match input_consumption with
                | some _ => none /- A path of consumption should not exist -/
                | none => some (some q, none)
              | some (Sum.inr (f2 : S → Option Q)) =>
                -- The machine popped the stack, got `x`, and decided to consume the input
                fun input_consumption => match input_consumption with
                | none => none /- Epsilon transition should not exist -/
                | some a => match f2 a with
                  | some q => some (some q, some x)
                  | none =>
                    /-
                      Raises an error in the original machine.
                      Since in Sipser we need to populate this, I implement this as a transition to the death trap state.
                    -/
                    some (none, none)
              | none =>
                -- The machine popped the stack, got `x`, and decided to raise an error.
                -- Since in Sipser we need to populate this, I implement this as an epsilon transition to the death trap state.
                fun input_consumption => match input_consumption with
                | none => some (none, none)
                | some _ => none /- A path of consumption should not exist -/
  let is_deterministic := by
    intro q a x
    simp only
    suffices h :
      exactly_one_some
        (sipser_delta_curried q (some x) (some a))
        (sipser_delta_curried q none (some a))
        (sipser_delta_curried q (some x) none)
        (sipser_delta_curried q none none) = true from h
    simp only [sipser_delta_curried]
    match q with
    | none => -- death trap state
      simp only [exactly_one_some]
    | some p =>
      match h : dot_delta p with
      | Predet_Judge.uncondPush (α, q2) =>
        simp only [exactly_one_some, h]
      | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>
        simp only [exactly_one_some, h]
        match h2 : fΓ_wS none with
        | some (Sum.inl q2) =>
          simp only
        | some (Sum.inr f2) =>
          simp only
          match h3 : f2 a with
          | some q => simp only
          | none => simp only
        | none =>
          simp only
          match fΓ_wS (some x) with
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
    some q0,
    Finset.image some F,
    fun (p, input_consumption, stack_consumption) => sipser_delta_curried p stack_consumption input_consumption
    ⟩,
    is_deterministic
  ⟩

theorem Predet_to_Sipser_preserves_semantics_single_step {Q S Γ}
  [Fintype Q] [DecidableEq Q] [Fintype S] [Fintype Γ] [DecidableEq Γ]
  (M: Predet_DPDA Q S Γ) (idesc: Predet_DPDA_IDesc Q S Γ) :
  Predet_DPDA_IDesc.toSipser <$> M.stepTransition idesc = M.toSipser.stepTransition idesc.toSipser := by
  simp [Functor.map,
  -- Predet_DPDA_IDesc.toSipser,     Predet_DPDA.toSipser,
  -- Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition,
  ]
  match h : M.transition idesc.p with
  | Predet_Judge.uncondPush (α, q) =>
    simp [Predet_DPDA_IDesc.toSipser, Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
    rw [h] -- This is where I got `motive is not type correct`
  | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS => sorry
