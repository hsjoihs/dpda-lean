import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option


-- Basically (fun u => u >>= f) but avoid using `>>=` directly
-- def flipBind {α} : (α → Option α) →  Option α → Option α := flip bind
def flipBind {α} (f : α → Option α) : Option α → Option α :=
  fun u =>
    match u with
    | none => none
    | some (a: α) => f a

lemma repeat_flipBind_map α β γ
  (η_o : α → β)
  (pick: γ → (α → Option α))
  (η_f : γ → (β → Option β))
  (g : γ)
  (th : ∀ a, ((pick g) a).map η_o = (η_f g) (η_o a))
  (n : Nat)
  (a : α) :
  Nat.repeat (flipBind (η_f g)) n (some (η_o a)) = (Nat.repeat (flipBind (pick g)) n (some a)).map η_o := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.repeat, flipBind, ih]
    cases h : Nat.repeat (flipBind (pick g)) n (some a) with
    | none => rfl
    | some a' =>
      simp only [Option.map_some]
      simp only [h, Option.map_some] at ih
      rw [← th a']
