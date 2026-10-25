module

public import SmallPresentation.PerfectificationOverlap
public import SmallPresentation.PerfectificationTietze
public import SmallPresentation.HomologySC

/-! The exact perfectification preserves torsion-free Schur multipliers. -/
@[expose] public section

namespace SmallPresentationStatements.Conversion.Relative

variable {k μ : ℕ}

theorem relativeGroup_schur_torsionFree (T : FP k μ)
    (hT : IsMulTorsionFree (Homology.Schur T.Group)) :
    IsMulTorsionFree (Homology.Schur (RelativeGroup T)) := by
  apply RelativeSmallCancellation.short_overlap_schur_torsionFree
    (FactorGroup T) (rowLength T) (rows T) (rows_nontrivial T) (rows_cyclically_reduced T)
    (fun i ↦ by have h := rowLength_ge T i; omega) (rows_triple_injective T)
  intro a
  cases a with
  | inl _ => exact hT
  | inr _ => exact Homology.cyclic_schur_torsionFree

theorem perfectification_schur_torsionFree (T : FP k μ)
    (hT : IsMulTorsionFree (Homology.Schur T.Group)) :
    IsMulTorsionFree (Homology.Schur (perfectification T).Group) := by
  let := relativeGroup_schur_torsionFree T hT
  let e := Homology.schurEquiv (equivPerfectification T)
  exact e.symm.injective.isMulTorsionFree e.symm.toMonoidHom

end SmallPresentationStatements.Conversion.Relative
