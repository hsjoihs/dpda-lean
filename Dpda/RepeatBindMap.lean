import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

lemma repeat_succ_outer {α} (f : α → α) (n : ℕ) (a : α) :
  Nat.repeat f (n + 1) a = f (Nat.repeat f n a) := by rfl

lemma repeat_succ_inner {α} (f : α → α) (n : ℕ) (a : α) :
  Nat.repeat f (n + 1) a = Nat.repeat f n (f a) := by
   induction n with
   | zero => rfl
   | succ d hd =>
      rw [repeat_succ_outer]
      nth_rw 2 [repeat_succ_outer]
      apply congr_arg
      exact hd

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
    simp only [Nat.repeat]
    rw [map_pure]
  | succ n ih =>
    simp only [Nat.repeat, ih, bind_map_left, map_bind, th]
