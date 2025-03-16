import Std.Data.HashSet
import Mathlib.Data.Multiset.Defs

variable {a : Type} [BEq a] [Hashable a] [EquivBEq a] [LawfulHashable a]

theorem Std.HashSet.emptyc_toList_eq_nil : (∅ : Std.HashSet a).toList = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [Std.HashSet.length_toList]
  exact Std.HashSet.size_emptyc

theorem Std.HashSet.distinct_toList_nodup [LawfulBEq a] (s : Std.HashSet a) : s.toList.Nodup := by
  apply Multiset.coe_nodup.mpr
  unfold List.Nodup
  refine (List.Pairwise.imp ?_ Std.HashSet.distinct_toList)
  intro a b
  simp
