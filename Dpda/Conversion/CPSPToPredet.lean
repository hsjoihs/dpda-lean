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

def CPSP_DPDA.toPredet {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [DecidableEq Q] (M: CPSP_DPDA Q S Γ)
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
    | some α =>
      let hj := j.prop
      let n := α.length
      if j = n - 1
        then Predet_Judge.uncondPush (α.get (⟨ 0 , sorry ⟩ : Fin α.length), QExpand.originalQ qb)
        else Predet_Judge.uncondPush
          (
            α.get (⟨n - j - 1, sorry ⟩ : Fin α.length),
            QExpand.newQ ⟨
              qa, qb, G, s, (⟨ j + 1, sorry ⟩ : Fin (match M.str qa qb G s with | none => 0 | some str => str.length) )
            ⟩
          )
  ⟨ sorry, sorry, transition ⟩
