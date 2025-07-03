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

def CPSP_DPDA.expandedQ {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] (M: CPSP_DPDA Q S Γ) : Type :=
  Q × Q × AugmentZ0 Γ × AugmentEpsilon S × Fin (M.max_string_length)

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
