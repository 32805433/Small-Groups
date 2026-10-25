module

public import SmallPresentation.FreeProductPresentation
public import SmallPresentation.HopfExact

/-! The integral Schur multiplier of an arbitrary indexed free product is the
direct sum of the factor multipliers. The proof uses the disjoint-union free
presentation, normal generation of its relations, and the factor retractions.
No small-cancellation, classifying-space, or homology admission is used. -/
@[expose] public section

namespace SmallPresentationStatements.Homology.FreeProductPresentation

open RelationExtension
open DirectSum
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {A : Type} (G : A → Type) [∀ a, Group (G a)]

/-- The sum of the actual factor maps into the disjoint-union presentation kernel. -/
noncomputable def hopfSum : (⨁ a, H₂ (G a)) →+ Additive (PresentationKernel (Relations G)) :=
  DirectSum.toAddMonoid (fun a ↦
    (presentationMap (canonicalRelations (G a)) (Relations G)
      (factor G a) (factor_relations G a)).toAdditive)

@[simp] theorem hopfSum_of (a : A) (x : H₂ (G a)) :
    hopfSum G (DirectSum.of (fun a ↦ H₂ (G a)) a x) =
      (presentationMap (canonicalRelations (G a)) (Relations G)
        (factor G a) (factor_relations G a)).toAdditive x := DirectSum.toAddMonoid_of _ _ _

/-- Forgetting derived-subgroup membership identifies the two factor inclusions. -/
theorem hopfSum_of_inclusion (a : A) (x : H₂ (G a)) :
    (hopfInclusion (Relations G)).toAdditive
      (hopfSum G (DirectSum.of (fun a ↦ H₂ (G a)) a x)) =
        (factorKernel G a).toAdditive ((hopfInclusion (canonicalRelations (G a))).toAdditive x) := by
  rw [hopfSum_of]
  rfl

/-- Every Hopf class comes from finitely many factor Hopf classes. -/
theorem hopfSum_surjective : Function.Surjective (hopfSum G) := by
  intro z
  obtain ⟨y, hy⟩ := relationSum_surjective G ((hopfInclusion (Relations G)).toAdditive z)
  have hderived (a : A) : (y a).toMul.val ∈
      commutator (Total (canonicalRelations (G a))) := by
    have hcomponent : (y a).toMul.val = retractionTotal G a z.toMul.val.val := by
      have h := relationSum_retraction G a y
      rw [hy] at h
      exact (congrArg (fun t : Additive (Kernel (canonicalRelations (G a))) ↦ t.toMul.val) h).symm
    rw [hcomponent]
    have hm : (commutator (Total (Relations G))).map (retractionTotal G a) ≤
        commutator (Total (canonicalRelations (G a))) := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    exact hm ⟨z.toMul.val.val, z.toMul.val.property, rfl⟩
  let w (a : A) : H₂ (G a) :=
    Additive.ofMul ⟨⟨(y a).toMul.val, hderived a⟩, (y a).toMul.property⟩
  let x : ⨁ a, H₂ (G a) := ∑ a ∈ y.support, DirectSum.of (fun a ↦ H₂ (G a)) a (w a)
  refine ⟨x, ?_⟩
  apply Additive.toMul.injective
  apply hopfInclusion_injective (Relations G)
  change (hopfInclusion (Relations G)).toAdditive (hopfSum G x) =
    (hopfInclusion (Relations G)).toAdditive z
  rw [← hy]
  calc
    (hopfInclusion (Relations G)).toAdditive (hopfSum G x) =
        ∑ a ∈ y.support, (factorKernel G a).toAdditive (y a) := by
      simp only [x, map_sum, hopfSum_of_inclusion]
      rfl
    _ = relationSum G (∑ a ∈ y.support,
        DirectSum.of (fun a ↦ Additive (Kernel (canonicalRelations (G a)))) a (y a)) := by
      simp only [map_sum, relationSum_of]
    _ = relationSum G y := by rw [DirectSum.sum_support_of]

/-- Naturality identifies the presentation calculation with the canonical Schur functor. -/
theorem hopfSum_comparison (x : ⨁ a, H₂ (G a)) :
    (hopfEquivOfPresentation (projection G) (projection_surjective G)).toAdditive
      (hopfSum G x) = freeProductSchurMap G x := by
  have h : (hopfEquivOfPresentation (projection G) (projection_surjective G)).toAdditive.toAddMonoidHom.comp
      (hopfSum G) = freeProductSchurMap G := by
    apply DirectSum.addHom_ext
    intro a z
    rw [AddMonoidHom.comp_apply, hopfSum_of, freeProductSchurMap_of]
    change hopfEquivOfPresentation (projection G) (projection_surjective G)
      (presentationMap _ _ (factor G a) (factor_relations G a) z.toMul) = _
    have hp : Function.Surjective (freeProjection (G a)) := by
      intro g
      exact ⟨FreeGroup.of g, by simp [freeProjection]⟩
    rw [hopfEquivOfPresentation_natural (freeProjection (G a)) (projection G)
      hp (projection_surjective G) (factor G a) (Monoid.CoprodI.of : G a →* _)
      (projection_factor G a) (factor_relations G a)]
    exact congrArg (schurMap (Monoid.CoprodI.of : G a →* _))
      (hopfEquivOfPresentation_canonical hp z.toMul)
  exact DFunLike.congr_fun h x

end SmallPresentationStatements.Homology.FreeProductPresentation

namespace SmallPresentationStatements.Homology

open DirectSum
attribute [local instance] Classical.propDecidable

variable {A : Type} (G : A → Type) [∀ a, Group (G a)]

/-- The canonical factor map is surjective for every indexed family of groups. -/
theorem freeProductSchurMap_surjective : Function.Surjective (freeProductSchurMap G) := by
  intro z
  let e := FreeProductPresentation.projection G
  obtain ⟨x, hx⟩ := FreeProductPresentation.hopfSum_surjective G
    ((hopfEquivOfPresentation e (FreeProductPresentation.projection_surjective G)).symm.toAdditive z)
  refine ⟨x, ?_⟩
  rw [← FreeProductPresentation.hopfSum_comparison, hx]
  exact (hopfEquivOfPresentation e (FreeProductPresentation.projection_surjective G)).toAdditive.apply_symm_apply z

/-- The Schur multiplier of an indexed free product is the direct sum of the multipliers. -/
theorem freeProductSchurMap_bijective : Function.Bijective (freeProductSchurMap G) :=
  ⟨freeProductSchurMap_injective G, freeProductSchurMap_surjective G⟩

/-- The canonical integral degree-two free-product decomposition. -/
noncomputable def freeProductSchurEquiv : (⨁ a, H₂ (G a)) ≃+ H₂ (Monoid.CoprodI G) :=
  AddEquiv.ofBijective (freeProductSchurMap G) (freeProductSchurMap_bijective G)

@[simp] theorem freeProductSchurEquiv_of (a : A) (x : H₂ (G a)) :
    freeProductSchurEquiv G (DirectSum.of (fun a ↦ H₂ (G a)) a x) =
      map₂ (Monoid.CoprodI.of : G a →* _) x := freeProductSchurMap_of G a x

end SmallPresentationStatements.Homology
