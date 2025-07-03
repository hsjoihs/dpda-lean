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

def CPSP_DPDA.max_string_length {Q S Γ} [Fintype Q] [Fintype S] [Fintype Γ] [BEq Q] [BEq S] [BEq Γ]
  (M: CPSP_DPDA Q S Γ) : Nat :=
  let candidates : Finset Nat := Finset.image (CPSP_Judge.max_string_length ∘ M.transition) Finset.univ
  match Finset.max candidates with
  | some maximum => maximum
  | none => 0
