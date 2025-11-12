import Mathlib.Logic.Embedding.Basic

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

def canonicalRepresentative [s : SetoidWithCanonicalizer α] : (Quotient s.toSetoid) ↪ α :=
  let emb := fun (q: Quotient s.toSetoid) => q.liftOn (SetoidWithCanonicalizer.canonicalize) (by
    intro r1 r2 h
    rw [SetoidWithCanonicalizer.equiv_then_canonicalize_eq r1 r2 h]
  )
  ⟨emb, by
    intro q1 q2 h
    induction q1 using Quotient.inductionOn with | _ repres1 =>
    induction q2 using Quotient.inductionOn with | _ repres2 =>
    dsimp only [emb, Quotient.lift_mk] at h
    apply Quotient.sound
    apply (SetoidWithCanonicalizer.canonicalize_eq_iff_equiv repres1 repres2).mp
    simpa
  ⟩

def canonicalRepresentative_section_of_quot
    [s : SetoidWithCanonicalizer α] (q: Quotient s.toSetoid) : ⟦canonicalRepresentative q⟧ = q := by
  induction q using Quotient.inductionOn with | _ repres =>
  apply Quotient.sound
  dsimp only [DFunLike.coe, canonicalRepresentative, Quotient.lift_mk]
  simp only [SetoidWithCanonicalizer.canonicalize_equiv_self]

end SetoidWithCanonicalizer
