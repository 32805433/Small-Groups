module

public import SmallPresentation.RelationDerivativeSchur
public import SmallPresentation.QuotientRelatorLifts

/-! Transport the weighted relation theorem to the actual free-product quotient.
The hypotheses are factor injection and weighted identity reduction in a free
presentation; the conclusion concerns the original quotient map on homology. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CanonicalSchur

open RelationCoordinates Homology

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (new : I → FreeGroup (Σ a, G a))

abbrev baseRelations := Relations (fun i ↦ FreeProductPresentation.projection G (new i))
abbrev BaseQuotient := Monoid.CoprodI G ⧸ baseRelations G new
abbrev baseQuotientMap := QuotientGroup.mk' (baseRelations G new)

/-- The equivalence from the actual quotient to its disjoint free presentation. -/
noncomputable def presentationEquiv : BaseQuotient G new ≃* Target G new :=
  QuotientRelatorLifts.equiv (FreeProductPresentation.projection G)
    (FreeProductPresentation.projection_surjective G) (old G) (sourceRelations_eq G) new

/-- The actual factor inclusion, transported into the lifted free presentation. -/
noncomputable def presentedFactor (a : A) : G a →* Target G new :=
  (presentationEquiv G new).toMonoidHom.comp
    ((baseQuotientMap G new).comp Monoid.CoprodI.of)

@[simp] theorem presentationEquiv_quotient_projection (w : FreeGroup (Σ a, G a)) :
    presentationEquiv G new (baseQuotientMap G new (FreeProductPresentation.projection G w)) =
      quotient G new w := by
  change QuotientRelatorLifts.baseLift (FreeProductPresentation.projection G)
    (FreeProductPresentation.projection_surjective G) (old G) (sourceRelations_eq G) new
    (FreeProductPresentation.projection G w) = _
  exact QuotientRelatorLifts.baseLift_apply _ _ _ _ _ w

/-- The transported inclusions respect all free generators. -/
theorem presentedFactor_compat (a : A) :
    (quotient G new).comp (FreeGroup.map (Sigma.mk a)) =
      (presentedFactor G new a).comp (factorProjection G a) := by
  apply FreeGroup.ext_hom
  intro g
  simpa [presentedFactor, factorProjection, freeProjection,
    FreeProductPresentation.projection] using
    (presentationEquiv_quotient_projection G new (FreeGroup.of ⟨a, g⟩)).symm

/-- Summing the transported inclusions gives the transported original quotient map. -/
theorem presentedFactor_lift : Monoid.CoprodI.lift (presentedFactor G new) =
    (presentationEquiv G new).toMonoidHom.comp (baseQuotientMap G new) := by
  apply Monoid.CoprodI.ext_hom
  intro a
  ext g
  simp [presentedFactor]

/-- Factor embeddings and weighted relative identity reduction imply injectivity
on degree-two homology for the original free-product quotient map. -/
theorem map₂_quotient_injective_of_weighted
    (hfactors : ∀ a, Function.Injective ((baseQuotientMap G new).comp
      (Monoid.CoprodI.of : G a →* Monoid.CoprodI G)))
    (hbalanced : Weighted.Balanced (all G new) (quotient G new) RelativeWeighted.newLabel) :
    Function.Injective (Homology.map₂ (baseQuotientMap G new)) := by
  have hi := map₂_lift_injective G new (presentedFactor G new)
    (presentedFactor_compat G new)
    (fun a ↦ (presentationEquiv G new).injective.comp (hfactors a)) hbalanced
  rw [presentedFactor_lift] at hi
  intro x y hxy
  apply hi
  rw [← Homology.map₂_comp, ← Homology.map₂_comp, hxy]

/-- The same theorem for any specified relators and any chosen lifts of them. -/
theorem map₂_quotient_injective_of_lifted_weighted
    (rel : I → Monoid.CoprodI G)
    (hnew : ∀ i, FreeProductPresentation.projection G (new i) = rel i)
    (hfactors : ∀ a, Function.Injective ((QuotientGroup.mk' (Relations rel)).comp
      (Monoid.CoprodI.of : G a →* Monoid.CoprodI G)))
    (hbalanced : Weighted.Balanced (all G new) (quotient G new) RelativeWeighted.newLabel) :
    Function.Injective (Homology.map₂ (QuotientGroup.mk' (Relations rel))) := by
  have hr : (fun i ↦ FreeProductPresentation.projection G (new i)) = rel := funext hnew
  subst rel
  exact map₂_quotient_injective_of_weighted G new hfactors hbalanced

end SmallPresentationStatements.RelationDerivative.CanonicalSchur
