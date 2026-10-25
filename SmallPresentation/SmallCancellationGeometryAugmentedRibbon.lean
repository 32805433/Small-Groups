module

public import SmallPresentation.SmallCancellationGeometryEulerComponent

/-!
# The actual parallel-arc augmentation of a ribbon

Replace each old dart by a leading and trailing marker. An edge becomes two parallel
edges, and each vertex boundary doubles. Leading face cycles are exactly the old edge
cycles; trailing face cycles are the old face cycles. This is the finite-map realization
of replacing a factor letter by `x_a g x_a⁻¹`.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

/-- Leading marker followed by trailing marker, then the next old vertex incidence. -/
def augmentedRotation : Equiv.Perm (D × Bool) where
  toFun
    | (d, false) => (d, true)
    | (d, true) => (P.rotation d, false)
  invFun
    | (d, false) => (P.rotation.symm d, true)
    | (d, true) => (d, false)
  left_inv := by rintro ⟨d, b⟩; cases b <;> simp
  right_inv := by rintro ⟨d, b⟩; cases b <;> simp

/-- Pair leading and trailing markers on the opposite original edge end. -/
def augmentedEdge : Equiv.Perm (D × Bool) where
  toFun d := (P.edge d.1, !d.2)
  invFun d := (P.edge d.1, !d.2)
  left_inv d := Prod.ext (P.edge_involutive d.1) (Bool.not_not d.2)
  right_inv d := Prod.ext (P.edge_involutive d.1) (Bool.not_not d.2)

def augmented : RibbonMap (D × Bool) where
  edge := P.augmentedEdge
  edge_involutive d := Prod.ext (P.edge_involutive d.1) (Bool.not_not d.2)
  edge_ne d h := by
    have hh := congrArg Prod.snd h
    change (!d.2) = d.2 at hh
    cases hb : d.2 <;> simp [hb] at hh
  rotation := P.augmentedRotation

@[simp] theorem augmented_rotation_false (d : D) :
    P.augmented.rotation (d, false) = (d, true) := rfl

@[simp] theorem augmented_rotation_true (d : D) :
    P.augmented.rotation (d, true) = (P.rotation d, false) := rfl

@[simp] theorem augmented_edge (d : D) (b : Bool) :
    P.augmented.edge (d, b) = (P.edge d, !b) := rfl

@[simp] theorem augmented_face_false (d : D) :
    P.augmented.face (d, false) = (P.edge d, false) := rfl

@[simp] theorem augmented_face_true (d : D) :
    P.augmented.face (d, true) = (P.face d, true) := rfl

/-- First projection sends each new vertex step into an old vertex cycle. -/
theorem augmented_rotation_projects (d : D × Bool) :
    P.rotation.SameCycle d.1 (P.augmented.rotation d).1 := by
  rcases d with ⟨d, b⟩
  cases b
  · exact .refl _ _
  · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- An old vertex step is exactly two new vertex steps. -/
theorem augmented_rotation_lifts (d : D) :
    P.augmented.rotation.SameCycle (d, false) (P.rotation d, false) := by
  have h₁ : P.augmented.rotation.SameCycle (d, false) (d, true) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have h₂ : P.augmented.rotation.SameCycle (d, true) (P.rotation d, false) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  exact h₁.trans h₂

noncomputable def augmentedVerticesEquiv [Finite D] : P.augmented.Vertex ≃ P.Vertex where
  toFun := Quotient.map Prod.fst (fun _ _ h ↦
    PermutationCycles.sameCycle_map_of_step _ _ Prod.fst P.augmented_rotation_projects h)
  invFun := Quotient.map (fun d ↦ (d, false)) (fun _ _ h ↦
    PermutationCycles.sameCycle_map_of_step _ _ (fun d ↦ (d, false))
      P.augmented_rotation_lifts h)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      apply Quotient.sound
      rcases d with ⟨d, b⟩
      cases b
      · exact .refl _ _
      · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  right_inv c := by induction c using Quotient.inductionOn with | h d => rfl

/-- Separate leading and trailing dart copies. -/
def augmentedCopies : D × Bool ≃ D ⊕ D where
  toFun
    | (d, false) => .inl d
    | (d, true) => .inr d
  invFun
    | .inl d => (d, false)
    | .inr d => (d, true)
  left_inv := by rintro ⟨d, b⟩; cases b <;> rfl
  right_inv := by intro d; cases d <;> rfl

/-- New faces consist exactly of one face per old edge and all old faces. -/
noncomputable def augmentedFacesEquiv [Finite D] :
    P.augmented.Face ≃ P.Edge ⊕ P.Face :=
  (PermutationCycles.conjugateEquiv P.augmented.face (Equiv.sumCongr P.edge P.face)
    augmentedCopies (by rintro ⟨d, b⟩; cases b <;> rfl)).trans
      (PermutationCycles.sumCyclesEquiv P.edge P.face)

theorem augmented_component_projects {d e : D × Bool}
    (h : P.augmented.SameComponent d e) : P.SameComponent d.1 e.1 := by
  apply P.augmented.map_components P Prod.fst ?_ ?_ h
  · intro x; exact P.component_edge x.1
  · rintro ⟨x, b⟩
    cases b
    · exact Relation.EqvGen.refl _
    · exact P.component_rotation x

theorem augmented_component_lifts {d e : D} (h : P.SameComponent d e) :
    P.augmented.SameComponent (d, false) (e, false) := by
  apply P.map_components P.augmented (fun d ↦ (d, false)) ?_ ?_ h
  · intro x
    exact Relation.EqvGen.trans _ _ _ (P.augmented.component_edge (x, false))
      (Relation.EqvGen.symm _ _ (P.augmented.component_rotation (P.edge x, false)))
  · intro x
    exact Relation.EqvGen.trans _ _ _ (P.augmented.component_rotation (x, false))
      (P.augmented.component_rotation (x, true))

noncomputable def augmentedComponentsEquiv : P.augmented.Component ≃ P.Component where
  toFun := Quotient.map Prod.fst (fun _ _ h ↦ P.augmented_component_projects h)
  invFun := Quotient.map (fun d ↦ (d, false)) (fun _ _ h ↦ P.augmented_component_lifts h)
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h d =>
      apply Quotient.sound
      rcases d with ⟨d, b⟩
      cases b
      · exact Relation.EqvGen.refl _
      · exact P.augmented.component_rotation (d, false)
  right_inv c := by induction c using Quotient.inductionOn with | h d => rfl

theorem augmented_card_vertices [Finite D] :
    Fintype.card P.augmented.Vertex = Fintype.card P.Vertex :=
  Fintype.card_congr P.augmentedVerticesEquiv

theorem augmented_card_faces [Finite D] :
    Fintype.card P.augmented.Face = Fintype.card P.Edge + Fintype.card P.Face := by
  simpa only [Fintype.card_sum] using Fintype.card_congr P.augmentedFacesEquiv

theorem augmented_card_edges [Fintype D] :
    Fintype.card P.augmented.Edge = 2 * Fintype.card P.Edge := by
  have h := P.augmented.card_darts
  rw [Fintype.card_prod, Fintype.card_bool, P.card_darts] at h
  omega

theorem augmented_card_components [Finite D] :
    Fintype.card P.augmented.Component = Fintype.card P.Component :=
  Fintype.card_congr P.augmentedComponentsEquiv

/-- Parallel-arc augmentation preserves the spherical Euler equation on all components. -/
theorem augmented_euler_iff [Fintype D] :
    (Fintype.card P.augmented.Vertex + Fintype.card P.augmented.Face =
      Fintype.card P.augmented.Edge + 2 * Fintype.card P.augmented.Component) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) := by
  rw [P.augmented_card_vertices, P.augmented_card_faces, P.augmented_card_edges,
    P.augmented_card_components]
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
