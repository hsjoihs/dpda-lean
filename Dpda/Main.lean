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

structure Predet_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  F : Finset Q
  transition : Predet_Transition Q S Γ

def Predet_Transition.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (transition: Predet_Transition Q S Γ)
  (pwβ: (Q × List S × List Γ))
  : Option ((Q × List S × List Γ)) := match transition pwβ.1 with
  | Predet_Judge.uncondPush (γ, q) => some ⟨q, pwβ.2.1, γ :: pwβ.2.2⟩
  | Predet_Judge.popAndDecideWhetherToConsume f =>
    match pwβ.2.2 with
    | [] => do
      let k ← f none
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.2.1)
      | Sum.inr f2 => match pwβ.2.1 with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, []⟩
    | A :: γ => do
      let k ← f (some A)
      let ⟨q, x⟩ ← match k with
      | Sum.inl q => some (q, pwβ.2.1)
      | Sum.inr f2 => match pwβ.2.1 with
        | [] => none
        | a :: t => match f2 a with
          | none => none
          | some q => some (q, t)
      some ⟨q, x, γ⟩

def Predet_DPDA.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (M: Predet_DPDA Q S Γ)
  (pwβ: (Q × List S × List Γ))
  : Option ((Q × List S × List Γ)) :=
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

def Sipser_DPDA.stepTransition {Q S Γ} (M: Sipser_DPDA Q S Γ) (pwβ: (Q × List S × List Γ)) : Option ((Q × List S × List Γ)) :=
  match hεε : M.pda.transition (pwβ.1, none, none) with
  | some (r, y) => some ⟨ r, pwβ.2.1, y.toList ++ pwβ.2.2 ⟩
  | none =>
    match pwβ.2.1, pwβ.2.2 with
    | [], [] => none
    | [], x :: xs =>
      match h2 : M.pda.transition (pwβ.1, none, some x) with
      | some (r, y) => some ⟨ r, pwβ.2.1, y.toList ++ xs ⟩
      | none => none
    | a :: ws, [] =>
      match h2 : M.pda.transition (pwβ.1, some a, none) with
      | some (r, y) => some ⟨ r, ws, y.toList ++ pwβ.2.2 ⟩
      | none => none
    | a :: ws, x :: xs =>
      match
        hax : (M.pda.transition (pwβ.1, some a, some x)),
        haε : (M.pda.transition (pwβ.1, some a, none)),
        hεx : (M.pda.transition (pwβ.1, none, some x)) with
      | some (r, y), none, none => some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none => some ⟨ r, pwβ.2.1, y.toList ++ xs ⟩
      | none, none, some (r, y) => some ⟨ r, ws, y.toList ++ pwβ.2.2 ⟩
      | some _, some _, some _ => False.elim <| by have h3 := M.deterministic pwβ.1 a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, some _, none   => False.elim <| by have h3 := M.deterministic pwβ.1 a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, none, some _   => False.elim <| by have h3 := M.deterministic pwβ.1 a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, some _, some _   => False.elim <| by have h3 := M.deterministic pwβ.1 a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, none, none       => False.elim <| by have h3 := M.deterministic pwβ.1 a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3


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
        | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS => sorry
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
  (M: Predet_DPDA Q S Γ) (idesc: (Q × List S × List Γ)) :
  (fun ⟨ p, w, β ⟩ => ⟨ some p, w, β ⟩) <$> M.stepTransition idesc = M.toSipser.stepTransition (idesc |> fun ⟨ p, w, β ⟩ => ⟨ some p, w, β ⟩) := by
  simp [Functor.map]
  match h : M.transition idesc.1 with
  | Predet_Judge.uncondPush (α, q) =>
    simp [Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
    rw [h] -- This is where I got `motive is not type correct`
  | Predet_Judge.popAndDecideWhetherToConsume fΓ_wS => sorry
