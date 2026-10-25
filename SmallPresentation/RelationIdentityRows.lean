module

public import SmallPresentation.RelationDerivativeRows
public import SmallPresentation.RelativeRelationDescent

/-! The scalar identity input for the literal rows follows from the same weighted
old/new identity condition that supplies the general homology injection. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.CanonicalSchur

open RelationCoordinates Homology RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)

/-- The exact scalar input needed by the existing small-cancellation theorem assembly. -/
theorem row_identity_balanced_of_weighted
    (hbalanced : RowWeightedBalanced G length rows) :
    IdentitySequencesBalanced (relatorValue G length rows) := by
  have h := QuotientRelatorLifts.scalar_descends (FreeProductPresentation.projection G)
    (FreeProductPresentation.projection_surjective G) (old G) (sourceRelations_eq G)
    (rowLift G length rows) hbalanced
  simpa only [projection_rowLift] using h

/-- The actual quotient retains the stronger, group-ring-valued identity balance. -/
theorem row_weighted_balanced_of_lifted
    (hbalanced : RowWeightedBalanced G length rows) :
    Weighted.Balanced (relatorValue G length rows)
      (QuotientGroup.mk' (relatorSubgroup G length rows)) (some : I → Option I) := by
  have h := QuotientRelatorLifts.weighted_descends (FreeProductPresentation.projection G)
    (FreeProductPresentation.projection_surjective G) (old G) (sourceRelations_eq G)
    (rowLift G length rows) hbalanced
  have he : (fun i ↦ FreeProductPresentation.projection G (rowLift G length rows i)) =
      relatorValue G length rows := funext (projection_rowLift G length rows)
  exact Eq.mp (congrArg (fun rel : I → Monoid.CoprodI G ↦
    Weighted.Balanced rel (QuotientGroup.mk' (Relations rel))
      (some : I → Option I)) he) h

end SmallPresentationStatements.RelationDerivative.CanonicalSchur
