module

public import SmallPresentation.Homology
public import Mathlib.Algebra.Module.Projective

/-! Canonical product coordinates for degree-one integral group homology. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G H : Type) [Group G] [Group H]

/-- Abelianization commutes with binary products, with the canonical projections. -/
def productH₁Equiv : H₁ (G × H) ≃+ H₁ G × H₁ H where
  toFun x := (map₁ (MonoidHom.fst G H) x, map₁ (MonoidHom.snd G H) x)
  invFun x := map₁ (MonoidHom.inl G H) x.1 + map₁ (MonoidHom.inr G H) x.2
  left_inv x := by
    obtain ⟨⟨g,h⟩, rfl⟩ := QuotientGroup.mk'_surjective (commutator (G × H)) x.toMul
    change Additive.ofMul (Abelianization.of (g,1) * Abelianization.of (1,h)) =
      Additive.ofMul (Abelianization.of (g,h))
    rw [← map_mul]
    simp
  right_inv x := by
    rcases x with ⟨x,y⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) x.toMul
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (commutator H) y.toMul
    change (Additive.ofMul (Abelianization.of (g*1)), Additive.ofMul (Abelianization.of (1*h))) =
      (Additive.ofMul (Abelianization.of g), Additive.ofMul (Abelianization.of h))
    simp
  map_add' x y := Prod.ext (map_add _ x y) (map_add _ x y)

@[simp] theorem productH₁Equiv_apply (x : H₁ (G × H)) :
    productH₁Equiv G H x = (map₁ (MonoidHom.fst G H) x, map₁ (MonoidHom.snd G H) x) := rfl

theorem productH₁_projective [Module.Projective ℤ (H₁ G)] [Module.Projective ℤ (H₁ H)] :
    Module.Projective ℤ (H₁ (G × H)) :=
  Module.Projective.of_equiv (productH₁Equiv G H).symm.toIntLinearEquiv

end SmallPresentationStatements.Homology
