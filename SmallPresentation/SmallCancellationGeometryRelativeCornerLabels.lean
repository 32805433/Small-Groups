module

public import SmallPresentation.SmallCancellationGeometryRelativeCornerWords

/-!
# Arc and coefficient transport for adjacent-corner cancellation

Deleting mutually inverse adjacent arcs across an identity corner preserves the evaluated
vertex word, after multiplying the following coefficient into the predecessor's corner.
This does not assert preservation of arbitrary face equations when a face is split.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

variable {D X H K : Type*} [Group H] [Group K] {P : RibbonMap D}
variable (C : AdjacentCancellation P) (L : RibbonLabelling P X H)

open Classical in
/-- Retain surviving arc letters and merge coefficients at the bypassed corner. -/
noncomputable def labelling (harc : L.arc C.right = reverseLetter (L.arc C.left)) :
    RibbonLabelling C.delete X H where
  arc d := L.arc d.val
  corner d := L.corner d.val * if P.rotation d.val = C.left then L.corner C.right else 1
  edge_arc d := by
    rw [C.edge_val_cases]
    by_cases hl : d.val = P.edge C.left
    · simp only [hl, ite_true, L.edge_arc, harc, reverseLetter_reverseLetter]
    · rw [ite_eq_right hl]
      by_cases hr : d.val = P.edge C.right
      · simp only [hr, ite_true, L.edge_arc, harc, reverseLetter_reverseLetter]
      · rw [ite_eq_right hr]
        exact L.edge_arc d.val

@[simp] theorem labelling_arc
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (d : C.Dart) :
    (C.labelling L harc).arc d = L.arc d.val := rfl

/-- The unchanged coefficients away from the predecessor of the deleted pair. -/
theorem labelling_corner_of_ne
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (d : C.Dart)
    (h : P.rotation d.val ≠ C.left) : (C.labelling L harc).corner d = L.corner d.val := by
  simp [labelling, h]

/-- The merged coefficient at the predecessor of the deleted pair. -/
theorem labelling_corner_of_eq
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (d : C.Dart)
    (h : P.rotation d.val = C.left) :
    (C.labelling L harc).corner d = L.corner d.val * L.corner C.right := by
  simp [labelling, h]

/-- At each surviving incidence, evaluation equals the complete accumulated original block.
The marker interpretation may take values in any group and coefficients map by any homomorphism. -/
theorem entry_value
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hcorner : L.corner C.left = 1)
    (marker : SignedLetter X → K) (hmarker : ∀ x, marker (reverseLetter x) = (marker x)⁻¹)
    (coefficient : H →* K) (d : C.Dart) :
    marker ((C.labelling L harc).arc d) * coefficient ((C.labelling L harc).corner d) =
      (C.blocks (fun e ↦ [marker (L.arc e) * coefficient (L.corner e)]) d).prod := by
  classical
  by_cases h : P.rotation d.val = C.left
  · simp [labelling, blocks, h, hcorner, harc, hmarker, mul_assoc]
  · simp [labelling, blocks, h]

/-- Evaluating any surviving based vertex word is unchanged by the actual two-corner surgery. -/
theorem vertex_value [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hcorner : L.corner C.left = 1)
    (marker : SignedLetter X → K) (hmarker : ∀ x, marker (reverseLetter x) = (marker x)⁻¹)
    (coefficient : H →* K) (d : C.Dart) :
    ((C.delete.vertexBoundary d).map (fun e ↦
      marker ((C.labelling L harc).arc e) * coefficient ((C.labelling L harc).corner e))).prod =
      ((P.vertexBoundary d.val).map (fun e ↦ marker (L.arc e) * coefficient (L.corner e))).prod := by
  have hh := congrArg List.prod (C.vertex_blocks
    (fun e ↦ [marker (L.arc e) * coefficient (L.corner e)]) d)
  simp only [List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def, List.prod_cons, List.prod_nil, mul_one] at hh
  rw [← hh]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e _
  exact C.entry_value L harc hcorner marker hmarker coefficient e

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
