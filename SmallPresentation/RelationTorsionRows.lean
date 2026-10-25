module

public import SmallPresentation.RelativeCyclicTorsion
public import SmallPresentation.RelationDerivativeRows

/-! Torsion preservation for the actual free-product quotient, derived from
factor embeddings and the same weighted identities used by the homology theorem. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CanonicalSchur

open RelationCoordinates Homology RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (new : I → FreeGroup (Σ a, G a))

/-- The original quotient of the free product is torsion-free under the reusable
weighted identity condition and the actual factor injections. -/
theorem torsionFree_quotient_of_weighted
    (hfactors : ∀ a, Function.Injective ((baseQuotientMap G new).comp
      (Monoid.CoprodI.of : G a →* Monoid.CoprodI G)))
    [∀ a, IsMulTorsionFree (G a)]
    (hbalanced : Weighted.Balanced (all G new) (quotient G new) RelativeWeighted.newLabel) :
    IsMulTorsionFree (BaseQuotient G new) := by
  let : IsMulTorsionFree (Target G new) := FactorSplitting.torsionFree_of_weighted
    G G (factorProjection G) new (presentedFactor G new) (presentedFactor_compat G new)
    (factorProjection_surjective G)
    (fun a ↦ (presentationEquiv G new).injective.comp (hfactors a)) hbalanced
  exact Function.Injective.isMulTorsionFree (presentationEquiv G new).toMonoidHom
    (presentationEquiv G new).injective

/-- The general theorem for specified base relators and any selected free lifts. -/
theorem torsionFree_quotient_of_lifted_weighted
    (rel : I → Monoid.CoprodI G)
    (hnew : ∀ i, FreeProductPresentation.projection G (new i) = rel i)
    (hfactors : ∀ a, Function.Injective ((QuotientGroup.mk' (Relations rel)).comp
      (Monoid.CoprodI.of : G a →* Monoid.CoprodI G)))
    [∀ a, IsMulTorsionFree (G a)]
    (hbalanced : Weighted.Balanced (all G new) (quotient G new) RelativeWeighted.newLabel) :
    IsMulTorsionFree (Monoid.CoprodI G ⧸ Relations rel) := by
  have hr : (fun i ↦ FreeProductPresentation.projection G (new i)) = rel := funext hnew
  subst rel
  exact torsionFree_quotient_of_weighted G new hfactors hbalanced

/-- The exact torsion conclusion required by the row-based small-cancellation API. -/
theorem rowQuotient_torsionFree_of_weighted
    (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)
    (hfactors : ∀ a, Function.Injective (factorMap G length rows a))
    [∀ a, IsMulTorsionFree (G a)]
    (hbalanced : RowWeightedBalanced G length rows) :
    IsMulTorsionFree (RelativeSmallCancellation.Quotient G length rows) := by
  exact torsionFree_quotient_of_lifted_weighted G (rowLift G length rows)
    (relatorValue G length rows) (projection_rowLift G length rows) hfactors hbalanced

end SmallPresentationStatements.RelationDerivative.CanonicalSchur
