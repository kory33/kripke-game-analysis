import Mathlib.Data.Finset.Basic

namespace Finset
end Finset

namespace Array

def setAtIndexPreservingLength (value : Fin n → α) (arr : { a : Array α // a.size = n }) (i : Fin n) : { a : Array α // a.size = n } :=
  ⟨arr.val.set i (value i), by simp only [size_set]; exact arr.property⟩

instance : RightCommutative (setAtIndexPreservingLength val) := {
  right_comm := by
    intro arr a1 a2
    simp only [Subtype.mk.injEq, setAtIndexPreservingLength]
    by_cases h : a1 = a2
    · rw [h]
    · rw [Array.set_comm (val a1) (val a2) (by revert h; contrapose!; exact Fin.eq_of_val_eq)]
}

lemma setAtIndexPreservingLength_eq {value : Fin n → α}
                                    {arr : { a : Array α // a.size = n }} {i j: Fin n} :
    (setAtIndexPreservingLength value arr i).val[j]'(by simp [(setAtIndexPreservingLength value arr i).property]) = if i = j then value i else arr.val[j] := by
  simp only [setAtIndexPreservingLength]
  by_cases h : i = j
  · simp [h]
  · simp only [Fin.getElem_fin, h, ↓reduceIte]
    rw [Array.getElem_set_ne _ _ _]
    simp [Fin.val_ne_of_ne h]

def setAtIndices (a : Array α) (a_size : a.size = n) (indices : Finset (Fin n)) (value : Fin n → α) : Array α :=
  (indices.val.foldl (setAtIndexPreservingLength value) ⟨a, a_size⟩).val

theorem setAtIndices_size : (setAtIndices a a_size indices value).size = a.size := by
  dsimp only [setAtIndices]
  set res := indices.val.foldl (setAtIndexPreservingLength value) ⟨a, a_size⟩
  rw [res.property, a_size]

theorem setAtIndices_eq (a : Array α) (a_size : a.size = n) :
    (setAtIndices a a_size indices value)[i]'(by simp [setAtIndices_size, a_size]) = if i ∈ indices then value i else a[i] := by
  dsimp only [setAtIndices]
  revert a
  induction indices using Finset.induction_on with
  | empty => simp
  | insert nextIndex restIndices headIndex_not_in_indices ih =>
      intro a a_size
      simp only [Finset.insert_val_of_notMem headIndex_not_in_indices]
      simp only [Multiset.foldl_cons, Finset.mem_insert]
      rw [ih _ _]
      by_cases h : i ∈ restIndices
      · simp [h]
      · simp only [h, ↓reduceIte, or_false]
        rw [setAtIndexPreservingLength_eq (value := value) (arr := ⟨a, a_size⟩) (i := nextIndex) (j := i)]
        by_cases h' : i = nextIndex
        · simp [h']
        · simp [h']; tauto

def setValueAtIndices {α : Type} (a : Array α) (a_size : a.size = n)
                         (indices : Finset (Fin n)) (value : α) : Array α :=
  setAtIndices a a_size indices (fun _ => value)

theorem setValueAtIndices_size {α : Type} (a : Array α) (a_size : a.size = n)
                                (indices : Finset (Fin n)) (value : α) :
    (setValueAtIndices a a_size indices value).size = a.size :=
  by exact setAtIndices_size

theorem setValueAtIndices_eq {α : Type} (a : Array α) (a_size : a.size = n)
                                (indices : Finset (Fin n)) (value : α) (i : Fin n) :
    (setValueAtIndices a a_size indices value)[i]'(by simp [setValueAtIndices_size, a_size]) =
    if i ∈ indices then value else a[i] :=
  by simp only [setValueAtIndices]; rw [setAtIndices_eq]

end Array
