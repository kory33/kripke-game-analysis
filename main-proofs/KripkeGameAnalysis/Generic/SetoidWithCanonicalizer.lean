class SetoidWithCanonicalizer (α : Type) extends Setoid α where
  canonicalize : α → α
  canonicalize_equiv_self : ∀ x, canonicalize x ≈ x
  equiv_then_canonicalize_eq : ∀ x y, x ≈ y → canonicalize x = canonicalize y

namespace SetoidWithCanonicalizer

theorem canonicalize_eq_iff_equiv [SetoidWithCanonicalizer α] (f f' : α) :
    canonicalize f = canonicalize f' ↔ f ≈ f' := by
  apply Iff.intro
  · intro h
    refine Setoid.trans (Setoid.symm (canonicalize_equiv_self f)) (Setoid.trans ?_ (canonicalize_equiv_self f'))
    simp [h, Setoid.refl]
  · exact equiv_then_canonicalize_eq f f'

end SetoidWithCanonicalizer
