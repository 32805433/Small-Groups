module

public import SmallPresentation.SmallCancellationGeometryCornerPotentials
public import SmallPresentation.SmallCancellationGeometryRelativeCornerLabels

/-!
# Based-path preservation under actual adjacent-corner deletion

The quotient potential is restricted to the surviving original incidences. At a reconnected
edge, its equality follows from the identity corner between the deleted marker pair.
The rotation law follows from multiplying the three bypassed corner steps.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CornerPotential

variable {D X H Q : Type*} [Group H] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {q : H →* Q} (F : CornerPotential L q)
    (C : AdjacentCancellation P)
    (harc : L.arc C.right = reverseLetter (L.arc C.left))
    (hcorner : L.corner C.left = 1)

include hcorner in
theorem adjacent_value_eq : F.value C.right = F.value C.left := by
  rw [← C.next, F.rotation, hcorner, map_one, mul_one]

/-- The same actual quotient paths satisfy the laws on the surgically reconnected ribbon. -/
noncomputable def cancel : CornerPotential (C.labelling L harc) q where
  value d := F.value d.val
  edge d := by
    classical
    rw [C.edge_val_cases]
    by_cases hl : d.val = P.edge C.left
    · rw [ite_eq_left hl, hl, F.edge, F.edge]
      exact F.adjacent_value_eq C hcorner
    · rw [ite_eq_right hl]
      by_cases hr : d.val = P.edge C.right
      · rw [ite_eq_left hr, hr, F.edge, F.edge]
        exact (F.adjacent_value_eq C hcorner).symm
      · rw [ite_eq_right hr]
        exact F.edge d.val
  rotation d := by
    classical
    rw [C.rotation_val]
    by_cases hl : P.rotation d.val = C.left
    · have hx : F.value C.left = F.value d.val * q (L.corner d.val) := by
        simpa only [hl] using F.rotation d.val
      rw [ite_eq_left hl, C.labelling_corner_of_eq L harc d hl,
        map_mul, F.rotation, F.adjacent_value_eq C hcorner, hx, mul_assoc]
    · rw [ite_eq_right hl, C.labelling_corner_of_ne L harc d hl]
      exact F.rotation d.val

@[simp] theorem cancel_value (d : C.Dart) : (F.cancel C harc hcorner).value d = F.value d.val := rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CornerPotential
