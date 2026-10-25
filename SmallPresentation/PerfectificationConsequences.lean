module

public import SmallPresentation.PerfectificationOverlap
public import SmallPresentation.PerfectificationTietze

/-! # The actual perfectification embeds its source and preserves torsion-freeness

These conclusions use the proved generic short-overlap
free-product theorem. The word hypotheses and the exact Tietze equivalence
are checked in the imported local modules.
-/
@[expose] public section

namespace SmallPresentationStatements.Conversion

variable {k μ : ℕ}

theorem perfectificationHom_injective (T : FP k μ) :
    Function.Injective (perfectificationHom T) := by
  have h := Relative.factorMap_injective T (.inl ())
  rw [← Relative.perfectToRelative_source T] at h
  exact fun x y hxy ↦ h (congrArg (Relative.perfectToRelative T) hxy)

theorem perfectification_torsionFree (T : FP k μ) (hT : IsMulTorsionFree T.Group) :
    IsMulTorsionFree (perfectification T).Group := by
  let : IsMulTorsionFree (Relative.RelativeGroup T) := Relative.relativeGroup_torsionfree T hT
  exact (Relative.equivPerfectification T).symm.injective.isMulTorsionFree
    (Relative.equivPerfectification T).symm.toMonoidHom

end SmallPresentationStatements.Conversion
