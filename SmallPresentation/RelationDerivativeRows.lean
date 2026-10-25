module

public import SmallPresentation.RelationDerivativeQuotient
public import SmallPresentation.SmallCancellationData

/-! Literal syllable lifts connect the reusable weighted Schur-injection theorem
to the row presentation used in the small-cancellation development. No geometric
small-cancellation theorem is assumed or invoked in the results below. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CanonicalSchur

open RelationCoordinates Homology RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)

/-- Read the syllables literally in the disjoint free generating alphabet. -/
def rowLift (i : I) : FreeGroup (Σ a, G a) :=
  (List.ofFn fun p ↦ FreeGroup.of (rows i p)).prod

@[simp] theorem projection_rowLift (i : I) :
    FreeProductPresentation.projection G (rowLift G length rows i) =
      relatorValue G length rows i := by
  simp [rowLift, relatorValue, includeSyllable, FreeProductPresentation.projection,
    map_list_prod, List.map_ofFn, Function.comp_def]

/-- Weighted identity reduction for the literal free lifts of the row relators. -/
abbrev RowWeightedBalanced : Prop :=
  Weighted.Balanced (all G (rowLift G length rows))
    (quotient G (rowLift G length rows)) RelativeWeighted.newLabel

/-- The exact conditional form needed by the metric Schur-injection theorem:
only factor injection and weighted geometric identity reduction remain inputs. -/
theorem map₂_rowQuotient_injective_of_weighted
    (hfactors : ∀ a, Function.Injective (factorMap G length rows a))
    (hbalanced : RowWeightedBalanced G length rows) :
    Function.Injective (Homology.map₂
      (QuotientGroup.mk' (relatorSubgroup G length rows))) := by
  exact map₂_quotient_injective_of_lifted_weighted G (rowLift G length rows)
    (relatorValue G length rows) (projection_rowLift G length rows) hfactors hbalanced

end SmallPresentationStatements.RelationDerivative.CanonicalSchur
