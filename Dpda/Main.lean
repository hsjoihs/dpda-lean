import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

universe u_

inductive Predet_Judge (Q: Type u_) (S: Type u_) (Γ: Type u_)
  | uncondPush : (Γ × Q) → Predet_Judge Q S Γ
  | popAndDecideWhetherToConsume : (Option Γ → Option (Q ⊕ (S → Option Q))) → Predet_Judge Q S Γ

abbrev Predet_Transition (Q: Type u_) (S: Type u_) (Γ: Type u_) :=
  Q → Predet_Judge Q S Γ

structure Predet_DPDA_IDesc (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  p : Q
  w : List S
  β : List Γ

structure Predet_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : Predet_Transition Q S Γ

def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) := match transition pwβ.p with
  | Predet_Judge.uncondPush (γ, q) => some ⟨q, pwβ.w, γ :: pwβ.β⟩
  | Predet_Judge.popAndDecideWhetherToConsume f =>
    match pwβ.β with
    | [] => do
      let k ← f none
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.w)
      | Sum.inr f2 => match pwβ.w with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, []⟩
    | A :: γ => do
      let k ← f (some A)
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.w)
      | Sum.inr f2 => match pwβ.w with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, γ⟩

def Predet_DPDA.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (M: Predet_DPDA Q S Γ)
  (pwβ: Predet_DPDA_IDesc Q S Γ)
  : Option (Predet_DPDA_IDesc Q S Γ) :=
  Predet_Transition.stepTransition M.transition pwβ


structure Sipser_PreDPDA (Q S Γ) where
  q0 : Q
  F : Finset Q
  transition : Q × Option S × Option Γ -> Option (Q × Option Γ)

def exactly_one_some {α}
  (o1 : Option α)
  (o2 : Option α)
  (o3 : Option α)
  (o4 : Option α) := match o1, o2, o3, o4 with
  | some _, none, none, none => true
  | none, some _, none, none => true
  | none, none, some _, none => true
  | none, none, none, some _ => true
  | _, _, _, _ => false

structure Sipser_DPDA(Q S Γ) where
  pda : Sipser_PreDPDA Q S Γ
  deterministic : ∀ q a x,
    exactly_one_some
      (pda.transition (q, some a, some x))
      (pda.transition (q, some a, none))
      (pda.transition (q, none, some x))
      (pda.transition (q, none, none))

structure Sipser_DPDA_IDesc (Q) (S) (Γ) where
  p : Q
  w : List S
  β : List Γ

def Sipser_DPDA.stepTransition {Q S Γ}
  (M: Sipser_DPDA Q S Γ)
  (pwβ: Sipser_DPDA_IDesc Q S Γ)
  : Option (Sipser_DPDA_IDesc Q S Γ) :=
  /-

  A Sipser DPDA has exactly one legal move in every situation where its stack is nonempty.
  If the stack is empty, a Sipser DPDA can move only if the transition function specifies a move that pops ε.
  -/

  match hεε : M.pda.transition (pwβ.p, none, none) with
  | some (r, y) =>
    -- If δ(q, ε, ε) is nonempty, there is no restriction on the input or stack.
    -- · move to the state r,
    -- · consume nothing from the input
    -- · pop nothing from the stack
    -- · push y onto the stack
    some ⟨ r, pwβ.w, y.toList ++ pwβ.β ⟩
  | none =>
    -- Otherwise, ∀ a x, exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`.
    -- Thus we first need to check whether the stack or the input is empty.
    match pwβ.w, pwβ.β with
    | [], [] =>
      -- If both the input and the stack are empty, we cannot move,
      -- since the only potential legal move, δ(q, ε, ε), turned out to be empty.
      none
    | [], x :: xs =>
      -- We cannot consume from an empty input, so our only hope is δ(q, ε, x), a transition without the input consumption.
      match h2 : M.pda.transition (pwβ.p, none, some x) with
      | some (r, y) =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none =>
        -- If δ(q, ε, x) is empty, we cannot move.
        none
    | a :: ws, [] =>
      -- If the stack is empty, our only legal option is δ(q, a, ε), a transition without the stack pop.
      match h2 : M.pda.transition (pwβ.p, some a, none) with
      | some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | none =>
        -- If δ(q, a, ε) is empty, we cannot move.
        none
    | a :: ws, x :: xs =>
      -- If both the input and the stack are nonempty, we have options.
      -- Exactly one of δ(q, a, x), δ(q, ε, x), or δ(q, a, ε) is `some`, and we have to choose the one that is `some`.
      match
        hax : (M.pda.transition (pwβ.p, some a, some x)),
        haε : (M.pda.transition (pwβ.p, some a, none)),
        hεx : (M.pda.transition (pwβ.p, none, some x)) with
      | some (r, y), none, none =>
        -- If δ(q, a, x) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop x from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none =>
        -- If δ(q, ε, x) is nonempty, we can pop x from the stack,
        -- move to the state r,
        -- consume nothing from the input,
        -- and push y onto the stack.
        some ⟨ r, pwβ.w, y.toList ++ xs ⟩
      | none, none, some (r, y) =>
        -- If δ(q, a, ε) is nonempty, we can consume a from the input,
        -- move to the state r,
        -- pop nothing from the stack,
        -- and push y onto the stack.
        some ⟨ r, ws, y.toList ++ pwβ.β ⟩
      | some _, some _, some _ => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, some _, none   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, none, some _   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, some _, some _   => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, none, none       => False.elim <| by have h3 := M.deterministic pwβ.p a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3

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
     | none => sorry

     | some p =>
       match dot_delta p with
        | Predet_Judge.uncondPush (α, q) => sorry
        | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS =>

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

            | some x => sorry
  let is_deterministic := sorry
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
