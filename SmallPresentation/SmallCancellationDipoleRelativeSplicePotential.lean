module

public import SmallPresentation.SmallCancellationDipoleRelativeSplice
public import SmallPresentation.SmallCancellationGeometryCornerPotentials

/-!
# Original quotient potentials through the anchor splice

The coefficient transferred at the anchor splice is exactly the correction required by the
new rotation. Every original quotient path value, including both ends of the anchor edge,
therefore survives unchanged.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CornerPotential

open PermutationCycles

variable {D X H Q : Type*} [Group H] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {q : H →* Q} (F : CornerPotential L q)

/-- The original marked quotient paths remain valid after merging across an actual edge. -/
noncomputable def edgeSplice (a : D) :
    CornerPotential (P.edgeSpliceLabelling L a) q where
  value := F.value
  edge := F.edge
  rotation d := by
    classical
    change F.value (cutAt P.rotation (P.rotation a) (P.edge a) d) =
      F.value d * q ((P.edgeSpliceLabelling L a).corner d)
    rw [cutAt_apply]
    by_cases ha : d = a
    · subst d
      rw [Equiv.swap_apply_left, F.edge]
      simp [RibbonMap.edgeSpliceLabelling]
    · have hr : P.rotation d ≠ P.rotation a := fun h ↦ ha (P.rotation.injective h)
      by_cases hp : d = P.face a
      · have he : P.rotation d = P.edge a := by
          rw [hp, RibbonMap.face_apply, Equiv.apply_symm_apply]
        rw [he, Equiv.swap_apply_right, F.rotation]
        have hv : F.value d * q (L.corner d) = F.value a := by
          rw [← F.rotation, he, F.edge]
        simp only [RibbonMap.edgeSpliceLabelling, ite_eq_right ha, ite_eq_left hp, map_mul]
        rw [← mul_assoc, hv]
      · have he : P.rotation d ≠ P.edge a := by
          intro h
          apply hp
          exact P.rotation.injective (h.trans (by simp [RibbonMap.face_apply]))
        rw [Equiv.swap_apply_of_ne_of_ne hr he, F.rotation]
        simp only [RibbonMap.edgeSpliceLabelling, ite_eq_right ha, ite_eq_right hp,
          mul_one]

@[simp] theorem edgeSplice_value (a : D) (d : D) :
    (F.edgeSplice a).value d = F.value d := rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CornerPotential
