import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

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
