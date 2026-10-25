module

public import SmallPresentation.RelationDerivativeSplitting
public import SmallPresentation.WeightedEquivariance

/-! Explicit quotient action on chosen coset copies of factor relation modules.
When representatives are compatible with a permutation of cosets, the action has
no internal coefficient twist. This is used with finite cyclic orbit representatives. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

open DirectSum RelationCoordinates
attribute [local instance] Classical.propDecidable

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a) (new : I → FreeGroup (Σ a, X a))
  (φ : ∀ a, G a →* Quotient X G p new)
  (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (p a))
  (C : ∀ a, CosetData (φ a))

@[simp] theorem cosetSum_of_class (a : A) (c : (C a).Index) (r : (p a).ker) :
    cosetSum X G p new φ compat C
      (DirectSum.of _ (⟨a, c⟩ : CosetIndex G φ C)
        (Additive.ofMul (Abelianization.of r))) =
      WeightedBasis.conjugateClass (all X G p new)
        (cosetWord X G (quotient X G p new) (QuotientGroup.mk'_surjective _) φ C ⟨a, c⟩)
        (Sum.inl ⟨a, r⟩) := by
  unfold cosetSum
  rw [AddMonoidHom.comp_apply, cosetRelationSum_of]
  exact moduleEquiv_conjugated_factor_of X G p new φ compat a _ r

/-- The action sends a coset copy to another with unchanged coefficient whenever
its representatives are related by literal left translation. -/
theorem quotientAction_cosetSum_of (q : Quotient X G p new) (a : A)
    (c d : (C a).Index) (hrep : (C a).representative d = q * (C a).representative c)
    (z : Additive (Abelianization (p a).ker)) :
    RelationAbelianization.quotientAction (Relations X G p new) q
      (cosetSum X G p new φ compat C (DirectSum.of _ ⟨a, c⟩ z)) =
      cosetSum X G p new φ compat C (DirectSum.of _ ⟨a, d⟩ z) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Relations X G p new) q
  induction z using QuotientGroup.induction_on with
  | H r =>
    change RelationAbelianization.quotientAction (Relations X G p new)
      (QuotientGroup.mk' (Relations X G p new) w)
      (cosetSum X G p new φ compat C (DirectSum.of _ ⟨a, c⟩
        (Additive.ofMul (Abelianization.of r)))) =
      cosetSum X G p new φ compat C (DirectSum.of _ ⟨a, d⟩
        (Additive.ofMul (Abelianization.of r)))
    rw [cosetSum_of_class, RelationAbelianization.quotientAction_mk,
      WeightedBasis.conjugationMap_conjugateClass]
    let v := cosetWord X G (quotient X G p new) (QuotientGroup.mk'_surjective _) φ C ⟨a, c⟩
    have hw : quotient X G p new (w * v) =
        (C a).representative d * φ a (p a 1) := by
      simp only [map_mul, v, cosetWord_projects, map_one, mul_one]
      exact hrep.symm
    have h := cosetSum_of_conjugation X G p new φ compat C a d 1 (w * v) hw r
    have he : relationConjugation (p a) 1 (Additive.ofMul (Abelianization.of r)) =
        Additive.ofMul (Abelianization.of r) := by
      rw [relationConjugation_of]
      congr 2
      apply Subtype.ext
      simp [kernelConjugation]
    rw [he] at h
    exact h.symm

end SmallPresentationStatements.RelationDerivative.FactorSplitting
