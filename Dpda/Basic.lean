import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

def lift {α} (f : α → Option α) : Option α → Option α :=
  fun u =>
    match u with
    | none => none
    | some (a: α) => f a

inductive AugmentZ0 Γ where
  | fromΓ : Γ → AugmentZ0 Γ
  | z0 : AugmentZ0 Γ
deriving DecidableEq

def equiv_fintype {α β} (eqv : α ≃ β) [ft : Fintype α] : Fintype β :=
  { elems := Fintype.elems.map eqv.toEmbedding,
    complete := by intro b; simp only [Finset.mem_map_equiv, ft.complete]
  }

def augmentZ0_option_equiv {Γ} : AugmentZ0 Γ ≃ Option Γ :=
  let toFn : AugmentZ0 Γ → Option Γ
      | AugmentZ0.fromΓ g => some g
      | AugmentZ0.z0 => none
  let backFn : Option Γ → AugmentZ0 Γ
      | none => AugmentZ0.z0
      | some g => AugmentZ0.fromΓ g
  { toFun := toFn, invFun := backFn,
    left_inv := by intro a; cases a <;> rfl,
    right_inv := by intro o; cases o <;> rfl }

instance AugmentZ0.fintype {Γ} [ft : Fintype Γ]: Fintype (AugmentZ0 Γ) := equiv_fintype augmentZ0_option_equiv.symm
