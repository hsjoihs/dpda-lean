structure Sipser_PreDPDA (Q S Γ) where
  /-
  q0 : Q
  F : Finset Q
  -/
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
  current_state : Q
  remaining_input : List S
  stack : List Γ


-- This is the version that does not depend on the `deterministic` condition.
-- This is intended as a workaround in Lean's `motive is not type correct` error.
def Sipser_PreDPDA.stepTransition {Q S Γ}
  (M: Sipser_PreDPDA Q S Γ)
  (idesc: Sipser_DPDA_IDesc Q S Γ)
  : Option (Sipser_DPDA_IDesc Q S Γ) :=
  match M.transition (idesc.current_state, none, none) with
  | some (r, y) => some ⟨ r, idesc.remaining_input, y.toList ++ idesc.stack ⟩
  | none => match idesc.remaining_input, idesc.stack with
    | [], [] => none
    | [], x :: xs => match M.transition (idesc.current_state, none, some x) with
      | some (r, y) => some ⟨ r, idesc.remaining_input, y.toList ++ xs ⟩
      | none => none
    | a :: ws, [] => match M.transition (idesc.current_state, some a, none) with
      | some (r, y) => some ⟨ r, ws, y.toList ++ idesc.stack ⟩
      | none => none
    | a :: ws, x :: xs => match
        (M.transition (idesc.current_state, some a, some x)),
        (M.transition (idesc.current_state, some a, none)),
        (M.transition (idesc.current_state, none, some x)) with
      | some (r, y), none, none => some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none => some ⟨ r, idesc.remaining_input, y.toList ++ xs ⟩
      | none, none, some (r, y) => some ⟨ r, ws, y.toList ++ idesc.stack ⟩
      | _, _, _ => none -- When the `deterministic` condition holds, this branch should never be reached.


def Sipser_DPDA.stepTransition {Q S Γ}
  (M: Sipser_DPDA Q S Γ)
  (idesc: Sipser_DPDA_IDesc Q S Γ)
  : Option (Sipser_DPDA_IDesc Q S Γ) :=
  match hεε : M.pda.transition (idesc.current_state, none, none) with
  | some (r, y) => some ⟨ r, idesc.remaining_input, y.toList ++ idesc.stack ⟩
  | none => match idesc.remaining_input, idesc.stack with
    | [], [] => none
    | [], x :: xs => match h2 : M.pda.transition (idesc.current_state, none, some x) with
      | some (r, y) => some ⟨ r, idesc.remaining_input, y.toList ++ xs ⟩
      | none => none
    | a :: ws, [] => match h2 : M.pda.transition (idesc.current_state, some a, none) with
      | some (r, y) => some ⟨ r, ws, y.toList ++ idesc.stack ⟩
      | none => none
    | a :: ws, x :: xs => match
        hax : (M.pda.transition (idesc.current_state, some a, some x)),
        haε : (M.pda.transition (idesc.current_state, some a, none)),
        hεx : (M.pda.transition (idesc.current_state, none, some x)) with
      | some (r, y), none, none => some ⟨ r, ws, y.toList ++ xs ⟩
      | none, some (r, y), none => some ⟨ r, idesc.remaining_input, y.toList ++ xs ⟩
      | none, none, some (r, y) => some ⟨ r, ws, y.toList ++ idesc.stack ⟩
      | some _, some _, some _ => False.elim <| by have h3 := M.deterministic idesc.current_state a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, some _, none   => False.elim <| by have h3 := M.deterministic idesc.current_state a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | some _, none, some _   => False.elim <| by have h3 := M.deterministic idesc.current_state a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, some _, some _   => False.elim <| by have h3 := M.deterministic idesc.current_state a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3
      | none, none, none       => False.elim <| by have h3 := M.deterministic idesc.current_state a x; simp [exactly_one_some, hεε, hax, haε, hεx] at h3


theorem step_in_pre_is_step_in_dpda {Q S Γ}
  (M: Sipser_DPDA Q S Γ)
  (idesc: Sipser_DPDA_IDesc Q S Γ) :
  Sipser_PreDPDA.stepTransition M.pda idesc = M.stepTransition idesc := by
  simp only [Sipser_PreDPDA.stepTransition, Sipser_DPDA.stepTransition]
  match h2 : M.pda.transition (idesc.current_state, none, none) with
  | some (r, y) => sorry
  | none => sorry
