import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Union

namespace Finset

theorem singleton_union_eq_insert {α : Type}
                                  [DecidableEq α]
                                  (s : Finset α) (a : α) : {a} ∪ s = insert a s := by
  apply Finset.ext; intro x; simp

end Finset
