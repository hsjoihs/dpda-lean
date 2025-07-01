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
