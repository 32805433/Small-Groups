module

public import SmallPresentation.ConversionRelationExtension
public import SmallPresentation.UniversalCentralExtension

/-! # Central closedness of the exact normalized finite presentation -/
public section

namespace SmallPresentationStatements.Conversion

/-- The generic universal-central-extension theorem applies to the actual perfect
quotient and the explicit isomorphism from the printed normalized rows. -/
theorem normalizedPresentation_centrallyClosed {k μ : ℕ} (T : FP k μ) :
    CentrallyClosed (normalizedPresentation T).Group := by
  have hperfect : commutator (FreeGroup (Fin 2) ⧸ perfectificationRelations T) = ⊤ :=
    perfectification_commutator_eq_top T
  exact (UniversalCentralExtension.relationDerived_centrallyClosed
    (perfectificationRelations T) hperfect).of_equiv (normalizedEquivRelationDerived T).symm

end SmallPresentationStatements.Conversion
