import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

lemma repeat_bind_map2 {m} [Monad m] [LawfulMonad m] α β
  (α2β : α → β)
  (mfα : α → m α)
  (mfβ : β → m β)
  (th : ∀ a, α2β <$> mfα a = mfβ (α2β a))
  (n : Nat)
  (a : α) :
  Nat.repeat (· >>= mfβ) n (pure (α2β a)) = α2β <$> Nat.repeat (· >>= mfα) n (pure a) := by
  induction n with
  | zero =>
    simp only [Nat.repeat, pure, bind_pure]
    rw [map_pure]
  | succ n ih =>
    simp only [Nat.repeat, ih, bind_map_left, map_bind, th]
