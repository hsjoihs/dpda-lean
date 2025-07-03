import Dpda.Definition.CharPopStringPush
import Dpda.Definition.PredeterminedToPushOrPop
import Mathlib.Data.Finset.Max

/-
  In converting from CPSP to Predet, each CPSP step translates into a sequence of Predet steps.
  First of all, this increases the number of overall states (that is, |Q|).
-/

def extract_string_length {Q Γ} (o : Option (List Γ × Q)) : Nat :=
  match o with
  | none => 0
  | some (s, _) => s.length

def CPSP_Judge.max_string_length {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ]
  (v: CPSP_Judge Q S Γ) : Nat :=
  match v with
  | CPSP_Judge.immediate none => 0
  | CPSP_Judge.immediate (some (α, _)) => α.length
  | CPSP_Judge.step f =>
    let candidates := Finset.image (extract_string_length ∘ f) Finset.univ
    match Finset.max candidates with
    | some maximum => maximum
    | none => 0

def CPSP_DPDA.max_string_length {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ]
  (M: CPSP_DPDA Q S Γ) : Nat :=
  let candidates : Finset Nat := Finset.image (CPSP_Judge.max_string_length ∘ M.transition) Finset.univ
  match Finset.max candidates with
  | some maximum => maximum
  | none => 0

def CPSP_DPDA.str {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q] (M: CPSP_DPDA Q S Γ)
  (qa : Q) (qb : Q) (G : AugmentZ0 Γ) (Sε : AugmentEpsilon S) : Option (List Γ) :=
  match Sε with
  | AugmentEpsilon.Epsilon =>
    match M.transition (qa, G) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some (α, q)) => if q = qb then some α else none
    | CPSP_Judge.step _ => none
  | AugmentEpsilon.fromChar a =>
    match M.transition (qa, G) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some _) => none
    | CPSP_Judge.step f => match f a with
      | none => none
      | some (α, q) => if q = qb then some α else none

inductive QExpand (Q: Type) (R: Type) where
  | originalQ : Q → QExpand Q R
  | newQ : R → QExpand Q R

def CPSP_DPDA.expandedQ {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q]
  (M: CPSP_DPDA Q S Γ) : Type
  := QExpand Q <|
    (qa : Q) ×
    (qb : Q) ×
    (G : AugmentZ0 Γ) ×
    (s : AugmentEpsilon S) ×
    Fin (match M.str qa qb G s with | none => 0 | some str => str.length)

instance {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q]
  (M: CPSP_DPDA Q S Γ) : Fintype (CPSP_DPDA.expandedQ M) where
    elems := sorry
    complete := sorry

theorem five_tuple {A B C D E} (t1 : A × B × C × D × E) (t2 : A × B × C × D × E) :
  t1 = t2 ↔
  t1.1 = t2.1 ∧
  t1.2.1 = t2.2.1 ∧
  t1.2.2.1 = t2.2.2.1 ∧
  t1.2.2.2.1 = t2.2.2.2.1 ∧
  t1.2.2.2.2 = t2.2.2.2.2 := by
  cases t1; cases t2; simp [Prod.ext_iff]

def myDecEq {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] [DecidableEq S]
  (M: CPSP_DPDA Q S Γ) (a b : CPSP_DPDA.expandedQ M) : Decidable (a = b) :=
  match a, b with
  | QExpand.originalQ qa, QExpand.originalQ qb =>
    if h : qa = qb then isTrue (by rw [h])
    else isFalse (by intro eq; cases eq; contradiction)
  | QExpand.newQ ⟨ qa, qb, G, s, j ⟩, QExpand.newQ ⟨ qa', qb', G', s', j' ⟩ =>
    if h2 : (qa, qb, G, s, (↑j : Nat)) = (qa', qb', G', s', (↑j' : Nat)) then
      isTrue (by
        simp [five_tuple] at h2
        apply congr_arg
        simp
        constructor
        · simp [h2]
        · sorry
          -- https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#HEq
          -- Heterogeneous equality. a ≍ b asserts that a and b have the same type,
          -- and casting a across the equality yields b, and vice versa.
          -- You should avoid using this type if you can.
      )
    else
      isFalse (by intro eq; cases eq; contrapose! h2; rfl)
  | QExpand.originalQ qa, QExpand.newQ ⟨ qa', qb', G', s', j' ⟩ =>
    isFalse (by simp only [reduceCtorEq, not_false_eq_true])
  | QExpand.newQ ⟨ qa, qb, G, s, j ⟩, QExpand.originalQ qb' =>
    isFalse (by simp only [reduceCtorEq, not_false_eq_true])

instance {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ] [DecidableEq S]
  (M: CPSP_DPDA Q S Γ) : DecidableEq (CPSP_DPDA.expandedQ M) := myDecEq M

def CPSP_DPDA.toPredet {Q S Γ}
  [Fintype Q] [Fintype S] [Fintype Γ]
  [DecidableEq Q] [DecidableEq Γ] [DecidableEq S]
 (M: CPSP_DPDA Q S Γ)
 : Predet_DPDA (M.expandedQ) S Γ :=
  let transition : M.expandedQ → Predet_Judge M.expandedQ S Γ := fun q => match q with
  | .originalQ qa => Predet_Judge.popAndDecideWhetherToConsume fun G =>
    match M.transition (qa, G) with
    | CPSP_Judge.immediate none => none
    | CPSP_Judge.immediate (some ([], qb)) => some (Sum.inl (QExpand.originalQ qb))
    | CPSP_Judge.immediate (some (α, qb)) =>
      some ∘ Sum.inl ∘ QExpand.newQ <| ⟨ qa, qb, G, AugmentEpsilon.Epsilon, Fin.mk 0 sorry ⟩
    | CPSP_Judge.step f => some <| Sum.inr fun a =>
      match f a with
      | some ([], qb) => some (QExpand.originalQ qb)
      | some (α, qb) => some (QExpand.newQ ⟨ qa, qb, G, AugmentEpsilon.fromChar a, Fin.mk 0 sorry ⟩ )
      | _ => none
  | .newQ ⟨ qa, qb, G, s, j ⟩  =>
    match hα : M.str qa qb G s with
    | none => by
      /- I do not have an off-the-path state as a member of M.expandedQ -/
      rw [hα] at j
      exact j.elim0
    | some [] => by
      /- "Empty string pushed to the stack" corresponds to not spawning a new state -/
      rw [hα] at j
      exact j.elim0
    | some α@h:(A :: γ) =>
      have len_pos : 0 < α.length := by simp [h]
      have len_nonzero : α.length ≠ 0 := by simp [h]
      if h_end : j = α.length - 1
        then Predet_Judge.uncondPush (α.get (⟨ 0 , len_pos ⟩ : Fin α.length), QExpand.originalQ qb)
        else
          have h_n1j : α.length - 1 - ↑j < α.length := by simp [h]; omega
          have h_j1 : (↑j : Nat) + 1 < (match M.str qa qb G s with
            | none => 0
            | some str => str.length) := by
            obtain u | u | u := lt_trichotomy ↑j (α.length - 1)
            · rw [← Nat.add_one_lt_add_one_iff, Nat.sub_one_add_one len_nonzero] at u
              simp [hα]
              simp [h] at u
              exact u
            · contradiction
            · simp [hα]
              simp [h] at u
              have hj2 := j.prop
              simp [hα] at hj2
              have hj3 : ↑j ≤ γ.length := by exact Nat.le_of_lt_add_one hj2
              have hj4 : ¬ (γ.length < ↑j) := by exact Nat.not_lt.mpr hj3
              contradiction
          Predet_Judge.uncondPush (
            α.get (⟨α.length - 1 - j, h_n1j ⟩ : Fin α.length),
            QExpand.newQ ⟨
              qa, qb, G, s, (⟨ j + 1, h_j1 ⟩ : Fin (match M.str qa qb G s with | none => 0 | some str => str.length) )
            ⟩
          )
  ⟨ QExpand.originalQ M.q0, Finset.image QExpand.originalQ M.F, transition ⟩
