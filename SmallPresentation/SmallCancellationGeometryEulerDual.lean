module

public import SmallPresentation.SmallCancellationGeometryEuler

/-! Dual ribbon maps exchange actual vertex and face cycles and preserve components. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

@[simp] theorem edge_symm_apply (d : D) : P.edge.symm d = P.edge d := by
  apply P.edge.injective
  rw [Equiv.apply_symm_apply, P.edge_involutive d]

@[simp] theorem face_symm_apply (d : D) : P.face.symm d = P.edge (P.rotation d) := by
  change P.edge.symm (P.rotation d) = _
  rw [P.edge_symm_apply]

/-- The dual uses the original face cycles as its vertex cycles. -/
def dual : RibbonMap D where
  edge := P.edge
  edge_involutive := P.edge_involutive
  edge_ne := P.edge_ne
  rotation := P.face

@[simp] theorem dual_edge : P.dual.edge = P.edge := rfl
@[simp] theorem dual_rotation : P.dual.rotation = P.face := rfl

theorem dual_face_apply (d : D) : P.dual.face d = P.edge (P.rotation (P.edge d)) := by
  exact P.face_symm_apply (P.edge d)

/-- Dual faces are original vertex cycles with edge ends interchanged. -/
noncomputable def dualFacesEquiv [Finite D] : P.dual.Face ≃ P.Vertex :=
  PermutationCycles.conjugateEquiv P.dual.face P.rotation P.edge (fun d ↦ by
    rw [P.dual_face_apply, P.edge_involutive])

theorem dual_sameComponent_iff (d e : D) :
    P.dual.SameComponent d e ↔ P.SameComponent d e := by
  constructor
  · intro h
    exact P.dual.map_components P id P.component_edge P.component_face h
  · intro h
    apply P.map_components P.dual id P.dual.component_edge ?_ h
    intro x
    have h₁ := P.dual.component_rotation_symm x
    have h₂ := P.dual.component_edge (P.dual.rotation.symm x)
    have ht := Relation.EqvGen.trans _ _ _ h₁ h₂
    change P.dual.SameComponent x (P.edge (P.face.symm x)) at ht
    rw [P.face_symm_apply, P.edge_involutive] at ht
    exact ht

noncomputable def dualComponentsEquiv : P.dual.Component ≃ P.Component :=
  Quotient.congr (Equiv.refl _) (fun d e ↦ P.dual_sameComponent_iff d e)

theorem dual_connected_iff : P.dual.Connected ↔ P.Connected := by
  simp only [Connected, P.dual_sameComponent_iff]

theorem card_dual_vertices [Finite D] : Fintype.card P.dual.Vertex = Fintype.card P.Face := rfl

theorem card_dual_faces [Finite D] : Fintype.card P.dual.Face = Fintype.card P.Vertex :=
  Fintype.card_congr P.dualFacesEquiv

theorem card_dual_edges [Finite D] : Fintype.card P.dual.Edge = Fintype.card P.Edge := rfl

theorem card_dual_components [Finite D] :
    Fintype.card P.dual.Component = Fintype.card P.Component :=
  Fintype.card_congr P.dualComponentsEquiv

/-- Spherical Euler characteristic on all components is invariant under duality. -/
theorem dual_euler_iff [Finite D] :
    (Fintype.card P.dual.Vertex + Fintype.card P.dual.Face =
      Fintype.card P.dual.Edge + 2 * Fintype.card P.dual.Component) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) := by
  rw [P.card_dual_vertices, P.card_dual_faces, P.card_dual_edges, P.card_dual_components]
  rw [add_comm]

/-- Inverse duality, chosen to restore the original labelled dart set exactly. -/
def undual : RibbonMap D where
  edge := P.edge
  edge_involutive := P.edge_involutive
  edge_ne := P.edge_ne
  rotation := P.rotation.symm.trans P.edge

@[simp] theorem undual_edge : P.undual.edge = P.edge := rfl

@[simp] theorem undual_rotation_apply (d : D) :
    P.undual.rotation d = P.edge (P.rotation.symm d) := rfl

@[simp] theorem undual_dual : P.undual.dual = P := by
  apply RibbonMap.ext
  · rfl
  · apply Equiv.ext
    intro d
    change P.rotation (P.edge.symm (P.edge d)) = P.rotation d
    rw [Equiv.symm_apply_apply]

@[simp] theorem dual_undual : P.dual.undual = P := by
  apply RibbonMap.ext
  · rfl
  · apply Equiv.ext
    intro d
    change P.edge (P.face.symm d) = P.rotation d
    rw [P.face_symm_apply, P.edge_involutive]

theorem undual_euler_iff [Finite D] :
    (Fintype.card P.undual.Vertex + Fintype.card P.undual.Face =
      Fintype.card P.undual.Edge + 2 * Fintype.card P.undual.Component) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) := by
  have h := P.undual.dual_euler_iff
  rw [P.undual_dual] at h
  exact h.symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
