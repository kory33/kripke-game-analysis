import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

def finsetEquivCharacteristic [Fintype α] [DecidableEq α] : Finset α ≃ (α → Bool) :=
{ toFun := fun s a => decide (a ∈ s),
  invFun := fun f => Finset.univ.filter (fun a => f a = true),
  left_inv := by intro s; simp,
  right_inv := by intro f; simp
}

def finsetProdEquivCurriedCharacteristic [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  : Finset (α × β) ≃ (α → β → Bool) :=
  finsetEquivCharacteristic.trans (Equiv.curry _ _ _)
