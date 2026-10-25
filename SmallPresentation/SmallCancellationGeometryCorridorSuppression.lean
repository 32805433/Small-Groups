module

public import SmallPresentation.SmallCancellationGeometryEulerDual
public import SmallPresentation.SmallCancellationGeometryBigonCounts
public import SmallPresentation.SmallCancellationGeometryBigonLabels

/-!
# Suppression of an actual degree-two corridor vertex

A non-isolated degree-two vertex is a bigon in the dual ribbon. Suppressing that bigon
and taking inverse duality reconnects its two incident edges. The remaining vertex rotation
is exactly the original rotation restricted to the surviving darts. Components and spherical
Euler characteristic are preserved. An isolated one-loop component is a separate case.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {D : Type*}

/-- A degree-two vertex whose two incident edge sides are not a single isolated loop. -/
structure DegreeTwoVertex (P : RibbonMap D) where
  left : D
  right : D
  ne : left ≠ right
  rotation_left : P.rotation left = right
  rotation_right : P.rotation right = left
  mate_ne_right : P.edge left ≠ right

namespace DegreeTwoVertex

variable {P : RibbonMap D} (C : DegreeTwoVertex P)

/-- The two opposite edge ends bound an actual bigon in the dual. -/
def dualBigon : Bigon P.dual where
  left := P.edge C.left
  right := P.edge C.right
  left_ne_right := P.edge.injective.ne C.ne
  mate_left_ne_right := by
    change P.edge (P.edge C.left) ≠ P.edge C.right
    rw [P.edge_involutive C.left]
    intro h
    apply C.mate_ne_right
    rw [h, P.edge_involutive C.right]
  face_left := by
    rw [P.dual_face_apply, P.edge_involutive C.left, C.rotation_left]
  face_right := by
    rw [P.dual_face_apply, P.edge_involutive C.right, C.rotation_right]

/-- The remaining incidences; exactly the two corridor darts have been deleted. -/
abbrev Dart := C.dualBigon.Dart

def dartEquiv : C.Dart ≃ {d : D // d ≠ C.left ∧ d ≠ C.right} where
  toFun d := ⟨d.val, by
    simpa only [dualBigon, RibbonMap.dual_edge, P.edge_involutive C.left,
      P.edge_involutive C.right] using d.property⟩
  invFun d := ⟨d.val, by
    simpa only [dualBigon, RibbonMap.dual_edge, P.edge_involutive C.left,
      P.edge_involutive C.right] using d.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reconnect the edge ends across the deleted corridor vertex. -/
noncomputable def suppress : RibbonMap C.Dart := C.dualBigon.suppress.undual

@[simp] theorem suppress_edge (d : C.Dart) :
    C.suppress.edge d = C.dualBigon.edge d := rfl

private theorem rotation_edge (d : C.Dart) :
    P.rotation (C.dualBigon.rotation d).val = (C.dualBigon.edge d).val := by
  classical
  rw [C.dualBigon.rotation_val]
  split_ifs with hl hr
  · have hd : d = C.dualBigon.leftDart := Subtype.ext hl
    rw [hd, C.dualBigon.edge_leftDart]
    change P.rotation (P.face (P.edge (P.edge C.right))) = P.edge C.right
    rw [P.edge_involutive C.right, RibbonMap.face_apply, Equiv.apply_symm_apply]
  · have hd : d = C.dualBigon.rightDart := Subtype.ext hr
    rw [hd, C.dualBigon.edge_rightDart]
    change P.rotation (P.face (P.edge (P.edge C.left))) = P.edge C.left
    rw [P.edge_involutive C.left, RibbonMap.face_apply, Equiv.apply_symm_apply]
  · rw [C.dualBigon.edge_val_of_ne d hl hr]
    change P.rotation (P.face d.val) = P.edge d.val
    rw [RibbonMap.face_apply, Equiv.apply_symm_apply]

/-- The new vertex rotation is literally the restriction of the original rotation. -/
theorem rotation_val (d : C.Dart) : (C.suppress.rotation d).val = P.rotation d.val := by
  have h := C.rotation_edge (C.dualBigon.rotation.symm d)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The corresponding old connected components are unchanged. -/
noncomputable def componentsEquiv : C.suppress.Component ≃ P.Component :=
  (C.dualBigon.suppress.undual.dualComponentsEquiv.symm.trans
    (Equiv.cast (congrArg RibbonMap.Component C.dualBigon.suppress.undual_dual))).trans
      (C.dualBigon.componentsEquiv.trans P.dualComponentsEquiv)

theorem card_components [Finite D] :
    Fintype.card C.suppress.Component = Fintype.card P.Component :=
  Fintype.card_congr C.componentsEquiv

/-- One corridor vertex and one edge disappear; the actual face count is unchanged. -/
theorem card_counts [Finite D] :
    Fintype.card P.Vertex = Fintype.card C.suppress.Vertex + 1 ∧
    Fintype.card P.Edge = Fintype.card C.suppress.Edge + 1 ∧
    Fintype.card P.Face = Fintype.card C.suppress.Face := by
  let := Fintype.ofFinite D
  have hv := C.dualBigon.card_vertices
  have hf := C.dualBigon.card_faces
  have he := C.dualBigon.card_edges
  have huv := C.suppress.card_dual_vertices
  have huf := C.suppress.card_dual_faces
  have hue := C.suppress.card_dual_edges
  have hu : C.suppress.dual = C.dualBigon.suppress :=
    C.dualBigon.suppress.undual_dual
  rw [hu] at huv huf hue
  rw [P.card_dual_vertices] at hv
  rw [P.card_dual_faces] at hf
  rw [P.card_dual_edges] at he
  omega

/-- Suppressing the corridor preserves the spherical Euler equation on all components. -/
theorem euler_iff [Finite D] :
    (Fintype.card C.suppress.Vertex + Fintype.card C.suppress.Face =
      Fintype.card C.suppress.Edge + 2 * Fintype.card C.suppress.Component) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) := by
  obtain ⟨hv, he, hf⟩ := C.card_counts
  rw [C.card_components]
  omega

end DegreeTwoVertex
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
