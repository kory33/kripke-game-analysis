class SetoidWithCanonicalizer (α : Type) extends Setoid α where
  canonicalize : α → α
  canonicalize_equiv_self : ∀ x, canonicalize x ≈ x
  equiv_then_canonicalize_eq : ∀ x y, x ≈ y → canonicalize x = canonicalize y

namespace SetoidWithCanonicalizer

theorem canonicalize_eq_iff_equiv [SetoidWithCanonicalizer α] (f f' : α) : canonicalize f = canonicalize f' ↔ f ≈ f' := by
  apply Iff.intro
  · intro h
    have p1 : f ≈ canonicalize f := Setoid.iseqv.symm (canonicalize_equiv_self f)
    rw [h] at p1
    exact (Setoid.iseqv.trans p1 (canonicalize_equiv_self f'))
  · exact SetoidWithCanonicalizer.equiv_then_canonicalize_eq f f'

end SetoidWithCanonicalizer
