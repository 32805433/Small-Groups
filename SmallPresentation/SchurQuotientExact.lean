module

public import SmallPresentation.QuotientFiveTerm
public import SmallPresentation.HopfNaturality

/-! The general five-term quotient sequence for the canonical Schur multiplier. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable {B : Type} [Group B] (N : Subgroup B) [N.Normal]

theorem freeProjection_surjective : Function.Surjective (freeProjection B) :=
  fun b ↦ ⟨FreeGroup.of b, FreeGroup.lift_apply_of⟩

namespace QuotientSequence

def quotientPresentation : FreeGroup B →* B ⧸ N :=
  (QuotientGroup.mk' N).comp (freeProjection B)

theorem quotientPresentation_surjective : Function.Surjective (quotientPresentation N) :=
  (QuotientGroup.mk'_surjective N).comp freeProjection_surjective

theorem quotientPresentation_ker :
    (quotientPresentation N).ker = relations (freeProjection B) N := by
  ext x
  exact QuotientGroup.eq_one_iff (freeProjection B x)

noncomputable def quotientHopfEquiv :
    PresentationKernel (relations (freeProjection B) N) ≃* Schur (B ⧸ N) :=
  hopfEquivWithKernel _ (quotientPresentation N) (quotientPresentation_surjective N)
    (quotientPresentation_ker N)

theorem quotientHopfEquiv_baseMap (x : Schur B) :
    quotientHopfEquiv N (baseMap (freeProjection B) N x) =
      schurMap (QuotientGroup.mk' N) x := by
  have h := hopfEquivWithKernel_natural (canonicalRelations B)
    (relations (freeProjection B) N) (freeProjection B) (quotientPresentation N)
    freeProjection_surjective (quotientPresentation_surjective N) rfl
    (quotientPresentation_ker N) (MonoidHom.id _) (QuotientGroup.mk' N) rfl
    (originalRelations_le (freeProjection B) N) x
  simpa only [hopfEquivWithKernel_canonical, quotientHopfEquiv, baseMap] using h

end QuotientSequence

/-- The canonical connecting map, defined by lifting to a free presentation.
Its domain is the actual Schur multiplier, not a chosen isomorphic surrogate. -/
noncomputable def quotientTransgression : Schur (B ⧸ N) →* RelationExtension.Kernel N :=
  (QuotientSequence.transgression (freeProjection B) N).comp
    (QuotientSequence.quotientHopfEquiv N).symm.toMonoidHom

theorem quotientTransgression_ker :
    (quotientTransgression N).ker = (schurMap (QuotientGroup.mk' N)).range := by
  apply le_antisymm
  · intro x hx
    have hh : (QuotientSequence.quotientHopfEquiv N).symm x ∈
        (QuotientSequence.transgression (freeProjection B) N).ker := hx
    rw [QuotientSequence.transgression_ker _ N freeProjection_surjective] at hh
    obtain ⟨y, hy⟩ := hh
    refine ⟨y, ?_⟩
    rw [← QuotientSequence.quotientHopfEquiv_baseMap, hy]
    exact (QuotientSequence.quotientHopfEquiv N).apply_symm_apply x
  · rintro _ ⟨x, rfl⟩
    change QuotientSequence.transgression (freeProjection B) N
      ((QuotientSequence.quotientHopfEquiv N).symm
        (schurMap (QuotientGroup.mk' N) x)) = 1
    rw [← QuotientSequence.quotientHopfEquiv_baseMap, MulEquiv.symm_apply_apply]
    exact QuotientSequence.transgression_baseMap _ N x

theorem quotientTransgression_range :
    (quotientTransgression N).range = (RelationExtension.boundary N).ker := by
  rw [QuotientSequence.boundary_ker _ N freeProjection_surjective]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨(QuotientSequence.quotientHopfEquiv N).symm x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨QuotientSequence.quotientHopfEquiv N x, ?_⟩
    change QuotientSequence.transgression (freeProjection B) N
      ((QuotientSequence.quotientHopfEquiv N).symm
        (QuotientSequence.quotientHopfEquiv N x)) = _
    rw [MulEquiv.symm_apply_apply]

/-- The full five-term exact sequence for an arbitrary normal quotient. -/
theorem quotient_five_term_exact :
    (quotientTransgression N).ker = (schurMap (QuotientGroup.mk' N)).range ∧
    (RelationExtension.boundary N).ker = (quotientTransgression N).range ∧
    (RelationExtension.abelianQuotient N).ker = (RelationExtension.boundary N).range ∧
    Function.Surjective (RelationExtension.abelianQuotient N) :=
  ⟨quotientTransgression_ker N, (quotientTransgression_range N).symm,
    RelationExtension.abelianQuotient_ker N, RelationExtension.abelianQuotient_surjective N⟩

end SmallPresentationStatements.Homology
