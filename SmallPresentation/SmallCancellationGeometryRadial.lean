module

public import SmallPresentation.SmallCancellationGeometryAugmentedRibbon
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler

/-!
# The radial ribbon joining original vertices to original faces

Each original corner becomes an edge. The two endpoint rotations are the original
vertex and face rotations. Each old edge becomes a four-corner radial face.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D : Type*} (P : RibbonMap D)

def radialRotation : Equiv.Perm (D × Bool) where
  toFun
    | (d, false) => (P.rotation d, false)
    | (d, true) => (P.face d, true)
  invFun
    | (d, false) => (P.rotation.symm d, false)
    | (d, true) => (P.face.symm d, true)
  left_inv := by
    rintro ⟨d, b⟩
    cases b <;> exact Prod.ext (Equiv.symm_apply_apply _ _) rfl
  right_inv := by
    rintro ⟨d, b⟩
    cases b <;> exact Prod.ext (Equiv.apply_symm_apply _ _) rfl

def radial : RibbonMap (D × Bool) where
  edge := {
    toFun := fun d ↦ (d.1, !d.2)
    invFun := fun d ↦ (d.1, !d.2)
    left_inv := fun d ↦ Prod.ext rfl (Bool.not_not d.2)
    right_inv := fun d ↦ Prod.ext rfl (Bool.not_not d.2) }
  edge_involutive d := Prod.ext rfl (Bool.not_not d.2)
  edge_ne d h := by
    have hh := congrArg Prod.snd h
    change (!d.2) = d.2 at hh
    cases hb : d.2 <;> simp [hb] at hh
  rotation := P.radialRotation

@[simp] theorem radial_edge (d : D) (b : Bool) : P.radial.edge (d, b) = (d, !b) := rfl
@[simp] theorem radial_rotation_false (d : D) :
    P.radial.rotation (d, false) = (P.rotation d, false) := rfl
@[simp] theorem radial_rotation_true (d : D) :
    P.radial.rotation (d, true) = (P.face d, true) := rfl
@[simp] theorem radial_face_false (d : D) :
    P.radial.face (d, false) = (P.face.symm d, true) := rfl
@[simp] theorem radial_face_true (d : D) :
    P.radial.face (d, true) = (P.rotation.symm d, false) := rfl

noncomputable def radialVerticesEquiv [Finite D] : P.radial.Vertex ≃ P.Vertex ⊕ P.Face :=
  (conjugateEquiv P.radial.rotation (Equiv.sumCongr P.rotation P.face)
    augmentedCopies (by rintro ⟨d, b⟩; cases b <;> rfl)).trans
      (sumCyclesEquiv P.rotation P.face)

/-- Project a radial face to the corresponding old edge. -/
def radialFaceCoordinate : D × Bool → D
  | (d, false) => P.rotation d
  | (d, true) => d

theorem radial_face_projects (x : D × Bool) :
    P.edge.SameCycle (P.radialFaceCoordinate x)
      (P.radialFaceCoordinate (P.radial.face x)) := by
  rcases x with ⟨d, b⟩
  cases b
  · change P.edge.SameCycle (P.rotation d) (P.face.symm d)
    rw [P.face_symm_apply]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  · change P.edge.SameCycle d (P.rotation (P.rotation.symm d))
    rw [Equiv.apply_symm_apply]

theorem radial_face_lifts (d : D) :
    P.radial.face.SameCycle (d, true) (P.edge d, true) := by
  have hs : P.radial.face (P.radial.face (d, true)) = (P.edge d, true) := by
    rw [radial_face_true, radial_face_false, P.face_symm_apply, Equiv.apply_symm_apply]
  rw [← hs]
  exact Equiv.Perm.sameCycle_apply_right.mpr
    (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))

noncomputable def radialFacesEquiv [Finite D] : P.radial.Face ≃ P.Edge where
  toFun := Quotient.map P.radialFaceCoordinate (fun _ _ h ↦
    sameCycle_map_of_step _ _ P.radialFaceCoordinate P.radial_face_projects h)
  invFun := Quotient.map (fun d ↦ (d, true)) (fun _ _ h ↦
    sameCycle_map_of_step _ _ (fun d ↦ (d, true)) P.radial_face_lifts h)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      apply Quotient.sound
      rcases d with ⟨d, b⟩
      cases b
      · change P.radial.face.SameCycle (P.rotation d, true) (d, false)
        have hs : P.radial.face (P.rotation d, true) = (d, false) := by
          rw [radial_face_true, Equiv.symm_apply_apply]
        rw [← hs]
        exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      · exact .refl _ _
  right_inv c := by induction c using Quotient.inductionOn with | h d => rfl

theorem radial_component_projects {d e : D × Bool}
    (h : P.radial.SameComponent d e) : P.SameComponent d.1 e.1 := by
  apply P.radial.map_components P Prod.fst ?_ ?_ h
  · intro x
    exact Relation.EqvGen.refl _
  · rintro ⟨x, b⟩
    cases b
    · exact P.component_rotation x
    · exact P.component_face x

theorem radial_component_lifts {d e : D} (h : P.SameComponent d e) :
    P.radial.SameComponent (d, false) (e, false) := by
  apply P.map_components P.radial (fun d ↦ (d, false)) ?_ ?_ h
  · intro x
    have h₁ := P.radial.component_edge (x, false)
    have h₂ := P.radial.component_rotation (x, true)
    have h₃ := P.radial.component_edge (P.face x, true)
    have h₄ := P.radial.component_rotation (P.face x, false)
    have hh := Relation.EqvGen.trans _ _ _ h₁ (Relation.EqvGen.trans _ _ _ h₂
      (Relation.EqvGen.trans _ _ _ h₃ h₄))
    change Relation.EqvGen P.radial.Adjacent (x, false) (P.edge x, false)
    simpa only [radial_edge, Bool.not_false, Bool.not_true, radial_rotation_true,
      radial_rotation_false, face_apply, Equiv.apply_symm_apply] using hh
  · intro x
    exact P.radial.component_rotation (x, false)

noncomputable def radialComponentsEquiv : P.radial.Component ≃ P.Component where
  toFun := Quotient.map Prod.fst (fun _ _ h ↦ P.radial_component_projects h)
  invFun := Quotient.map (fun d ↦ (d, false)) (fun _ _ h ↦ P.radial_component_lifts h)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      apply Quotient.sound
      rcases d with ⟨d, b⟩
      cases b
      · exact Relation.EqvGen.refl _
      · exact P.radial.component_edge (d, false)
  right_inv c := by induction c using Quotient.inductionOn with | h d => rfl

theorem radial_connected (hc : P.Connected) : P.radial.Connected := by
  intro d e
  have hd : P.radial.SameComponent d (d.1, false) := by
    rcases d with ⟨d, b⟩
    cases b
    · exact Relation.EqvGen.refl _
    · exact P.radial.component_edge (d, true)
  have he : P.radial.SameComponent (e.1, false) e := by
    rcases e with ⟨e, b⟩
    cases b
    · exact Relation.EqvGen.refl _
    · exact P.radial.component_edge (e, false)
  exact Relation.EqvGen.trans _ _ _ hd
    (Relation.EqvGen.trans _ _ _ (P.radial_component_lifts (hc d.1 e.1)) he)

theorem radial_card_vertices [Finite D] :
    Fintype.card P.radial.Vertex = Fintype.card P.Vertex + Fintype.card P.Face := by
  simpa only [Fintype.card_sum] using Fintype.card_congr P.radialVerticesEquiv

theorem radial_card_faces [Finite D] : Fintype.card P.radial.Face = Fintype.card P.Edge :=
  Fintype.card_congr P.radialFacesEquiv

theorem radial_card_edges [Fintype D] : Fintype.card P.radial.Edge = Fintype.card D := by
  have h := P.radial.card_darts
  rw [Fintype.card_prod, Fintype.card_bool] at h
  omega

theorem radial_card_components [Finite D] :
    Fintype.card P.radial.Component = Fintype.card P.Component :=
  Fintype.card_congr P.radialComponentsEquiv

/-- Radial expansion preserves spherical Euler characteristic without connectivity assumptions. -/
theorem radial_euler_iff [Fintype D] : P.radial.EulerEquality ↔ P.EulerEquality := by
  unfold EulerEquality
  rw [P.radial_card_vertices, P.radial_card_faces, P.radial_card_edges,
    P.radial_card_components, P.card_darts]
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
