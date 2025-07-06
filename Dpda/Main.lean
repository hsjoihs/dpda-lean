universe u_

structure Predet_DPDA (Q: Type u_) (S: Type u_) (Γ: Type u_) where
  q0 : Q
  transition : Q → (Γ × Q) ⊕ Fin 42

def Predet_DPDA.stepTransition {Q: Type u_} {S: Type u_} {Γ: Type u_}
  (M: Predet_DPDA Q S Γ)
  (pwβ: (Q × List S × List Γ))
  : Option ((Q × List S × List Γ)) := match M.transition pwβ.1 with
  | Sum.inl (γ, q) => some ⟨q, pwβ.2.1, γ :: pwβ.2.2⟩
  | Sum.inr f => sorry

structure Sipser_PreDPDA (Q S Γ) where
  q0 : Q
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

def Predet_DPDA.toSipser {Q S Γ} [DecidableEq Q] (M: Predet_DPDA Q S Γ) : Sipser_DPDA (Option Q) S Γ :=
  let ⟨ q0, dot_delta ⟩ := M
  let sipser_delta_curried : (Option Q) → Option Γ → Option S → Option (Option Q × Option Γ) :=
    fun p_ => match p_ with
     | none => sorry
     | some p =>
       match dot_delta p with
        | Sum.inl (α, q) => sorry
        | Sum.inr fΓ_wS => sorry
  let is_deterministic := sorry
  ⟨
    ⟨
    some q0,
    fun (p, input_consumption, stack_consumption) => sipser_delta_curried p stack_consumption input_consumption
    ⟩,
    is_deterministic
  ⟩

theorem Predet_to_Sipser_preserves_semantics_single_step {Q S Γ}
  [DecidableEq Q] [DecidableEq Γ]
  (M: Predet_DPDA Q S Γ) (idesc: (Q × List S × List Γ)) :
  (fun ⟨ p, w, β ⟩ => ⟨ some p, w, β ⟩) <$> M.stepTransition idesc = M.toSipser.stepTransition (idesc |> fun ⟨ p, w, β ⟩ => ⟨ some p, w, β ⟩) := by
  simp [Functor.map]
  match h : M.transition idesc.1 with
  | Sum.inl (α, q) =>
    simp [Predet_DPDA.toSipser, Predet_DPDA.stepTransition, Sipser_DPDA.stepTransition]
    rw [h] -- This is where I got `motive is not type correct`
  | Sum.inr fΓ_wS => sorry
