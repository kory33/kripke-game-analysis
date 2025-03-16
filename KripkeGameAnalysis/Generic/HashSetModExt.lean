import KripkeGameAnalysis.GenericExtras.HashSet
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.MapFold
import Batteries.Data.List.Perm

def HashSetExtensionality {α : Type} [BEq α] [Hashable α] [Hashable α] : Setoid (Std.HashSet α) where
  r := fun s t => ∀ x, (x ∈ s) = (x ∈ t)
  iseqv := {
    refl := by intros; trivial
    symm := by
      intro s t h x
      exact (h x).symm
    trans := by
      intro s t u hst htu x
      rw [hst x]
      exact htu x
  }

abbrev HashSetModExt (α : Type) [BEq α] [Hashable α] : Type := Quotient (HashSetExtensionality (α := α))
namespace HashSetModExt

section
variable {α : Type} [BEq α] [Hashable α]

def empty : HashSetModExt α := ⟦∅⟧
instance : EmptyCollection (HashSetModExt α) := ⟨empty⟩

theorem emptyc_toList_eq_nil [EquivBEq α] [LawfulHashable α]: (∅ : Std.HashSet α).toList = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [Std.HashSet.length_toList]
  exact Std.HashSet.size_emptyc

end

section
variable {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]

def toFinset (s : HashSetModExt α) : Finset α :=
  s.liftOn (fun s => {
    val := s.toList,
    nodup := Std.HashSet.distinct_toList_nodup s
  }) (by
    intro s t s_ext_t
    suffices _ : s.toList.Perm t.toList by simpa
    rw [List.perm_ext_iff_of_nodup (Std.HashSet.distinct_toList_nodup s) (Std.HashSet.distinct_toList_nodup t)]
    intro a
    simp only [Std.HashSet.mem_toList, s_ext_t a]
  )

end

section
variable {α : Type} [BEq α] [Hashable α]

def contains (s : HashSetModExt α) (a : α) : Bool :=
  s.liftOn (a ∈ ·) (by intro _ _ e; simp [e a])

instance : Membership α (HashSetModExt α) where
  mem s a := contains s a

@[simp] theorem contains_iff_mem {s : Std.HashSet α}
                                 {a : α} : (a ∈ (⟦s⟧ : HashSetModExt α)) = (a ∈ s) := by
  simp only [instMembership, contains, Quotient.lift_mk, decide_eq_true_eq]

@[ext] theorem ext (s t : HashSetModExt α) (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := by
  revert h
  apply s.ind; apply t.ind
  intro s_repr t_repr h
  apply Quot.sound
  intro a
  rw [←contains_iff_mem, ←contains_iff_mem, h]

end

section
variable {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] [LawfulBEq α]

def insert (s : HashSetModExt α) (a : α) : HashSetModExt α :=
  s.liftOn (fun s => ⟦s.insert a⟧) (by
    intro s t s_ext_t
    apply Quot.sound; intro x
    simp only [Std.HashSet.mem_insert, s_ext_t x]
  )

@[simp] theorem mem_insert { m: HashSetModExt α } { k a : α } : (a ∈ insert m k) ↔ (a == k ∨ a ∈ m) := by
  apply m.ind; intro hs
  suffices _ : k = a ∨ a ∈ hs ↔ a = k ∨ a ∈ hs by simpa [insert]
  tauto

instance insert_instRightCommutative: (RightCommutative (insert : HashSetModExt α -> α -> HashSetModExt α)) := by
  apply RightCommutative.mk; intro s a b; ext x
  simp only [mem_insert, beq_iff_eq]
  tauto

def insertAllOfFinset (s : HashSetModExt α) (fs : Finset α) : HashSetModExt α :=
  fs.val.foldl insert s

theorem mem_insertAllOfFinset { m: HashSetModExt α } { fs : Finset α }
                              { a : α } : (a ∈ insertAllOfFinset m fs) ↔ (a ∈ fs ∨ a ∈ m) := by
  dsimp only [insertAllOfFinset, Finset.instMembership]
  induction fs.val using Multiset.induction generalizing m
  next => simp
  next fs_head fs ih =>
    clear * - ih
    simp only [Multiset.foldl_cons, ih, mem_insert, beq_iff_eq, Multiset.mem_cons]
    tauto
end

end HashSetModExt
