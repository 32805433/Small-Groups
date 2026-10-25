module

public import SmallPresentation.SmallCancellationDipoleRelativePotentials
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsFaces
public import SmallPresentation.SmallCancellationGeometryRelativeCornerProducts

/-!
# Coefficient face products under degree-two suppression

The exact face boundary is the old boundary with the two interior corners removed. When
both interior coefficients are one, suppression retains the full noncommutative face
product, not merely its image in a quotient.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

open PermutationCycles

variable {D E H : Type*} [Finite D] [Finite E] [Group H]
    (P : RibbonMap D) (R : RibbonMap E) (e : D ≃ E)
    (he : ∀ d, e (P.edge d) = R.edge (e d))
    (hr : ∀ d, e (P.rotation d) = R.rotation (e d))

include he hr in
omit [Finite E] in
/-- Relabeling every actual incidence transports its complete face coefficient product. -/
theorem face_product_relabel (w : E → H) (d : D) :
    ((P.faceBoundary d).map (fun a ↦ w (e a))).prod =
      ((R.faceBoundary (e d)).map w).prod := by
  have hs (a : D) : e (P.face a) = R.face (e a) := by
    apply R.rotation.injective
    rw [← hr, RibbonMap.face_apply, Equiv.apply_symm_apply, he,
      RibbonMap.face_apply, Equiv.apply_symm_apply]
  have hb := cycleBoundary_map_injective P.face R.face e e.injective hs d
  change ((cycleBoundary P.face d).map (w ∘ e)).prod = _
  rw [← List.map_map, hb]
  rfl

end RibbonMap

namespace DegreeTwoVertex

open PermutationCycles

variable {D H : Type*} [Finite D] [Group H] {P : RibbonMap D} (C : DegreeTwoVertex P)

/-- Trivial interior corner coefficients are deleted without changing any surviving face product. -/
theorem suppress_face_product (w : D → H) (hl : w C.left = 1) (hr : w C.right = 1)
    (d : C.Dart) :
    ((C.suppress.faceBoundary d).map (fun a ↦ w a.val)).prod =
      ((P.faceBoundary d.val).map w).prod := by
  classical
  change ((C.suppress.faceBoundary d).map (w ∘ Subtype.val)).prod = _
  rw [← List.map_map, C.faceBoundary_filter]
  apply prod_filter_of_trivial_deleted
  intro a _ ha
  have hh : a = C.left ∨ a = C.right := by
    simpa only [decide_eq_false_iff_not, not_and_or, not_not] using ha
  rcases hh with rfl | rfl
  · exact hl
  · exact hr

end DegreeTwoVertex
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
