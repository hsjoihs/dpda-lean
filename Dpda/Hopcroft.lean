import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Dpda.CharPopStringPush

-- Hopcroft's DPDA definition [Introduction to Automata Theory, Languages, and Computation 3rd edition (page 252)]

structure Hopcroft_PreDPDA (Q S Γ) where
  q0 : Q
  z0 : Γ
  F : Finset Q
  -- criterion #1: $\delta(q,a,X)$ has at most one member for any $q$ in $Q$, $a$ in $\Sigma$ or $a = \varepsilon$, and $X$ in $\Gamma$.
  transition : Q × Option S × Γ -> Option (Q × List Γ)

structure Hopcroft_DPDA(Q S Γ) where
  pda : Hopcroft_PreDPDA Q S Γ
  -- criterion #2: If $\delta(q,a,X)$ is nonempty, for some $a$ in $\Sigma$, then $\delta(q, \varepsilon, X)$ must be empty.
  deterministic : ∀ q X, (∃ a, pda.transition (q, some a, X) ≠ none) → pda.transition (q, none, X) = none

inductive AugmentOneState Q
  | fromQ : Q → AugmentOneState Q
  | qNeg1 : AugmentOneState Q
deriving DecidableEq

def Hopcroft_DPDA.Δ {Q S Γ} (M: Hopcroft_DPDA Q S Γ) : Q × Γ → CPSP_Judge (AugmentOneState Q) S Γ :=
  fun (q, X) =>
    match M.pda.transition (q, none, X) with
    | some (p, α) => CPSP_Judge.immediate (some (α, AugmentOneState.fromQ p))
    | none => CPSP_Judge.step fun a =>
      match M.pda.transition (q, some a, X) with
      | some (p, α) => some (α, AugmentOneState.fromQ p)
      | none => none

def Hopcroft_DPDA.toCPSP {Q S Γ} [DecidableEq Q] [DecidableEq Γ] (M: Hopcroft_DPDA Q S Γ) : CPSP_DPDA (AugmentOneState Q) S Γ :=
  let q_neg1 : AugmentOneState Q := AugmentOneState.qNeg1
  let F : Finset (AugmentOneState Q) := Finset.image (fun (q: Q) => AugmentOneState.fromQ q) M.pda.F
  let new_transition : CPSP_Transition (AugmentOneState Q) S Γ := fun ⟨q', X⟩ =>
    match q', X with
    | AugmentOneState.qNeg1, .z0 =>
      CPSP_Judge.immediate (some
        (M.pda.z0 :: [], AugmentOneState.fromQ M.pda.q0)
      ) -- protect the stack bottom
    | AugmentOneState.qNeg1, .fromΓ _ => CPSP_Judge.immediate none -- stack shall be empty at the start
    | AugmentOneState.fromQ _, .z0 => CPSP_Judge.immediate none -- stack shall never be empty later
    | AugmentOneState.fromQ q, .fromΓ x => Hopcroft_DPDA.Δ M ⟨q, x⟩
  ⟨q_neg1, F, new_transition⟩

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

structure Hopcroft_DPDA_IDesc(Q S Γ) where
  p : Q
  w : List S
  β : List Γ

def Hopcroft_DPDA.stepTransition {Q S Γ} [DecidableEq Q] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ)
  (pwβ: Hopcroft_DPDA_IDesc Q S Γ)
  : Option (Hopcroft_DPDA_IDesc Q S Γ) :=
  let transition := M.pda.transition
  -- When δ(q, some a, X) contains (p, α),
  --     (q, aw, Xβ) ⊢ (p, w, α ++ β).
  -- When δ(q, none, X) contains (p, α),
  --     (q, w, Xβ) ⊢ (p, w, α ++ β).
  match pwβ.β with
  | .nil => none /-
    This path is implicitly assumed to be unreachable, but we must nevertheless handle it.
    Hopcroft's model assumes that we can *trust* the machine's designer,
    such that the stack never becomes empty:
    the expectation is that, as a *social norm*, one must replenish Z₀ after consuming Z₀ from the stack. -/
  | X :: β =>
    match transition (pwβ.p, none, X) with
    | some (p, α) =>
      /-
      -- If δ(q, none, X) is nonempty, we can use the epsilon transition.
      -- In particular, thanks to the deterministic condition (criterion #2; M.pda.deterministic),
      -- we know that δ(q, some a, X) is empty for any a in S.
      -- Thus the only option is to use the epsilon transition.

      -- Note that this reasoning does not need to be proven formally; we can simply assume it.
      -- We DO need it in order to prove that Hopcroft's DPDA is a subset of Hopcroft's non-deterministic DPDA.
      -/
      some ⟨p, pwβ.w, α ++ β⟩
    | none =>
      /-
      -- If δ(q, none, X) is empty, we must use the transition that consumes a symbol from the input.
      -/
      match pwβ.w with
      | .nil => none -- cannot consume from an empty input
      | a :: w' => match transition (pwβ.p, some a, X) with
        | some (p, α) => some ⟨p, w', α ++ β⟩
        | none => none

def Hopcroft_DPDA.run_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (w: List S) (n: ℕ) : Option (Hopcroft_DPDA_IDesc Q S Γ) :=
  let step : Hopcroft_DPDA_IDesc Q S Γ -> Option (Hopcroft_DPDA_IDesc Q S Γ) := Hopcroft_DPDA.stepTransition M
  Nat.repeat (lift step) n
    (some ⟨M.pda.q0, w, M.pda.z0 :: []⟩)

def Hopcroft_DPDA.membership_provable_in_n_steps {Q S Γ} [Fintype Q] [DecidableEq Q] [Fintype S /- Σ -/] [Fintype Γ] [DecidableEq Γ]
  (M: Hopcroft_DPDA Q S Γ) (w: List S) (n: ℕ) : Bool :=
    match Hopcroft_DPDA.run_n_steps M w n with
    | none => false
    | some idesc => (idesc.p ∈ M.pda.F)  && (idesc.w.length == 0)


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


inductive StackSymbol2 : Type
| A : StackSymbol2
| Z₀ : StackSymbol2
deriving Ord, BEq, DecidableEq, Repr

instance StackSymbol2.fintype : Fintype StackSymbol2 :=
  open StackSymbol2 in ⟨⟨{A, Z₀}, by simp⟩, fun x => by cases x <;> simp⟩

def Hopcroft_PreDPDA_anbn : Hopcroft_PreDPDA (Fin 3) Char_ StackSymbol2 where
  q0 := 0
  z0 := StackSymbol2.Z₀
  F := {2}
  transition := fun (q, u, γ) =>
    match q, u, γ with
    | 0, none, _ => none -- no epsilon transition in state 0
    | 0, some .a, .A => some (0, [StackSymbol2.A, StackSymbol2.A]) -- consume 'a' and push A onto the stack
    | 0, some .b, .A => some (1, []) -- pop A and move to state 1
    | 0, some .a, .Z₀ => some (0, [StackSymbol2.A, StackSymbol2.Z₀]) -- consume 'a' and push A onto the stack
    | 0, some .b, .Z₀ => none -- cannot consume 'b' in state 0 when the stack is empty
    | 1, some .a, .A => none -- cannot consume 'a' in state 1
    | 1, some .b, .A => some (1, []) -- consume 'b' and stay in state 1
    | 1, none, .A => none -- no epsilon transition in state 1 with A on the stack
    | 1, some .a, .Z₀ => none -- cannot consume 'a' in state 1 when the stack is empty
    | 1, some .b, .Z₀ => none -- cannot consume 'b' in state 1 when the stack is empty
    | 1, none, .Z₀ => some (2, [StackSymbol2.Z₀]) -- stack is empty; move to the final state
    | 2, _, _ => none -- final state, no transitions

def Hopcroft_DPDA_anbn : Hopcroft_DPDA (Fin 3) Char_ StackSymbol2 where
  pda := Hopcroft_PreDPDA_anbn
  deterministic := by
    intros q X h
    match q with
    | 0 => simp [Hopcroft_PreDPDA_anbn]
    | 2 => simp [Hopcroft_PreDPDA_anbn]
    | 1 => match X with
     | .A => simp [Hopcroft_PreDPDA_anbn]
     | .Z₀ =>
        rcases h with ⟨char, h⟩
        match char with
        | .a => simp [Hopcroft_PreDPDA_anbn] at h
        | .b => simp [Hopcroft_PreDPDA_anbn] at h

def STEP := 4
def STRING := [Char_.a, Char_.a, Char_.b, Char_.b]

def foo := CPSP_DPDA.run_n_steps CPSP_DPDA_anbn STRING STEP
#eval match foo with | some ⟨p, _, _⟩ => some p | none => none
#eval match foo with | some ⟨_, w, _⟩ => some w | none => none
#eval match foo with | some ⟨_, _, β⟩ => some β | none => none

def hop := Hopcroft_DPDA.run_n_steps Hopcroft_DPDA_anbn STRING STEP
#eval match hop with | some ⟨p, _, _⟩ => some p | none => none
#eval match hop with | some ⟨_, w, _⟩ => some w | none => none
#eval match hop with | some ⟨_, _, β⟩ => some β | none => none
