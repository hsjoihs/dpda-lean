import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option

universe u

def lift {α} (f : α → Option α) : Option α → Option α :=
  fun u =>
    match u with
    | none => none
    | some (a: α) => f a

-- $\Gamma_{Z} = \Gamma \cup \{ Z_0 \} $
inductive AugmentZ0 (Γ: Type u) where
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

-- $\Gamma_\varepsilon := \{ j \in \Gamma^* \mid \operatorname{len}(j) \le 1 \} \cong \Gamma \cup \{ \varepsilon \} $
inductive AugmentEpsilon (Γ: Type u) where
  | fromΓ : Γ → AugmentEpsilon Γ
  | Epsilon : AugmentEpsilon Γ
deriving DecidableEq


def augmentEpsilon_option_equiv {Γ} : AugmentEpsilon Γ ≃ Option Γ :=
  let toFn : AugmentEpsilon Γ → Option Γ
      | AugmentEpsilon.fromΓ g => some g
      | AugmentEpsilon.Epsilon => none
  let backFn : Option Γ → AugmentEpsilon Γ
      | none => AugmentEpsilon.Epsilon
      | some g => AugmentEpsilon.fromΓ g
  { toFun := toFn, invFun := backFn,
    left_inv := by intro a; cases a <;> rfl,
    right_inv := by intro o; cases o <;> rfl }

instance AugmentEpsilon.fintype {Γ} [ft : Fintype Γ]: Fintype (AugmentEpsilon Γ) := equiv_fintype augmentEpsilon_option_equiv.symm

def AugmentEpsilon.toList {Γ} (α: AugmentEpsilon Γ) : List Γ :=
  match α with
  | AugmentEpsilon.fromΓ g => [g]
  | AugmentEpsilon.Epsilon => []
