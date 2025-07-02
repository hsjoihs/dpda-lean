import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option


-- Avoid using `>>=` or `bind` directly, to reduce the necessity of `unfold`.
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

lemma repeat_bind_map {m} [Monad m] [LawfulMonad m] α β γ
  (η_o : α → β)
  (pick: γ → (α → m α))
  (η_f : γ → (β → m β))
  (g : γ)
  (th : ∀ a, η_o <$> ((pick g) a) = (η_f g) (η_o a))
  (n : Nat)
  (a : α) :
  Nat.repeat (· >>= η_f g) n (pure (η_o a)) = η_o <$> Nat.repeat (· >>= pick g) n (pure a) := by
  induction n with
  | zero =>
    simp only [Nat.repeat, pure, bind_pure]
    rw [map_pure]
  | succ n ih =>
    simp only [Nat.repeat, ih, bind_map_left, map_bind, th]
