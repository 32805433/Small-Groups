module

public import SmallPresentation.SmallCancellationGeometryCorridorMergeCycles
public import SmallPresentation.SmallCancellationGeometryCornerCancellationComponents
public import SmallPresentation.PermutationCycleProducts

/-! The two exceptional regions produced by an actual component-splitting cancellation. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} (P : RibbonMap D)

/-- A single cut in a connected graph has only the two distinguished possible components. -/
theorem vertexCut_component_cover (hc : P.Connected) (a b d : D)
    (hs : ¬(P.vertexCut a b).SameComponent a b) :
    (P.vertexCut a b).SameComponent d a ∨ (P.vertexCut a b).SameComponent d b := by
  classical
  let Q := P.vertexCut a b
  by_cases hd : Q.componentClass d = Q.componentClass b
  · exact Or.inr ((Q.componentClass_eq_iff d b).mp hd)
  · have ha : Q.componentClass a ≠ Q.componentClass b := fun h ↦ hs (Quotient.exact h)
    have hh := P.cutCollapseClass_constant a b hs (hc d a)
    have hv := congrArg Subtype.val hh
    dsimp only [Q] at hd ha
    simp only [cutCollapseClass, dite_eq_right hd, dite_eq_right ha] at hv
    exact Or.inl (Quotient.exact hv)

/-- For a genuine cut within one vertex of a spherical ribbon, the component separates
exactly when the two predecessor corners belonged to the same original face. -/
theorem vertexCut_components_iff_same_face [Fintype D] (a b : D) (hne : a ≠ b)
    (hvertex : P.rotation.SameCycle a b) (hE : P.EulerEquality) :
    ¬(P.vertexCut a b).SameComponent a b ↔
      P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b) := by
  constructor
  · exact P.vertexCut_face_sameCycle_of_split a b
  · intro hf hc
    have hv := P.vertexCut_card_vertices_of_sameCycle a b hne hvertex
    have hfaces : Fintype.card (P.vertexCut a b).Face = Fintype.card P.Face + 1 := by
      let := Fintype.ofFinite (PermutationCycles.Cycles
        (PermutationCycles.cutAt P.face (P.rotation.symm a) (P.rotation.symm b)))
      have hh := PermutationCycles.card_cutAt_of_sameCycle P.face
        (P.rotation.symm a) (P.rotation.symm b) (P.rotation.symm.injective.ne hne) hf
      have he := Fintype.card_congr (Equiv.cast (congrArg PermutationCycles.Cycles
        (P.vertexCut_face a b)))
      exact he.trans hh
    have hcomp := Fintype.card_congr (P.vertexCutComponentsEquiv a b
      (P.component_of_vertexCycle hvertex) hc)
    have hu := (P.vertexCut a b).euler_upper_bound
    change Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
    have hedge : Fintype.card (P.vertexCut a b).Edge = Fintype.card P.Edge := rfl
    omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

/-- The corner preceding the deleted pair survives unless that pair was the whole vertex. -/
def beforeDart (ht : P.rotation C.right ≠ C.left) : C.Dart :=
  ⟨P.rotation.symm C.left, by
    constructor
    · intro he
      have hh := congrArg P.rotation he
      rw [Equiv.apply_symm_apply, C.next] at hh
      exact C.ne hh
    · intro he
      have hh := congrArg P.rotation he
      rw [Equiv.apply_symm_apply] at hh
      exact ht hh.symm⟩

/-- The opposite end of the first edge survives in the non-loop case. -/
def mateDart (hn : P.edge C.left ≠ C.right) : C.Dart :=
  ⟨P.edge C.left, P.edge_ne C.left, hn⟩

theorem split_face_mate : C.split.face (P.edge C.left) = C.right := by
  apply C.split.rotation.injective
  change C.split.rotation (C.split.rotation.symm (P.edge (P.edge C.left))) =
    C.split.rotation C.right
  rw [Equiv.apply_symm_apply, P.edge_involutive C.left, C.split_rotation_right]

/-- At a genuine vertex split, the old affected face is one cycle exactly when the
cut separates the component. The Euler hypothesis is essential in this converse. -/
theorem split_components_iff_same_face [Fintype D] (ht : P.rotation C.right ≠ C.left)
    (hE : P.EulerEquality) :
    ¬C.split.SameComponent C.left (P.rotation C.right) ↔
      P.face.SameCycle (P.rotation.symm C.left) C.right := by
  have hv : P.rotation.SameCycle C.left (P.rotation C.right) := by
    have hh : P.rotation.SameCycle C.left (P.rotation (P.rotation C.left)) :=
      Equiv.Perm.sameCycle_apply_right.mpr
        (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    simpa only [C.next] using hh
  simpa only [split, Equiv.symm_apply_apply] using
    P.vertexCut_components_iff_same_face C.left (P.rotation C.right) ht.symm hv hE

/-- The two surviving affected face representatives lie on opposite sides exactly when
the preliminary cut splits the component. -/
theorem separated_regions_iff (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left ≠ C.right) :
    ¬C.delete.SameComponent (C.beforeDart ht) (C.mateDart hn) ↔
      ¬C.split.SameComponent C.left (P.rotation C.right) := by
  rw [C.sameComponent_iff]
  have h₁ : C.split.SameComponent (P.rotation.symm C.left) (P.rotation C.right) := by
    have hh := C.split.component_rotation (P.rotation.symm C.left)
    have hr : C.split.rotation (P.rotation.symm C.left) = P.rotation C.right :=
      P.vertexCut_rotation_predecessor_left C.left (P.rotation C.right)
    rw [hr] at hh
    exact hh
  have h₂ : C.split.SameComponent (P.edge C.left) C.left := by
    exact Relation.EqvGen.symm _ _ (C.split.component_edge C.left)
  apply not_congr
  change C.split.SameComponent (P.rotation.symm C.left) (P.edge C.left) ↔ _
  constructor
  · intro h
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ h₁) (Relation.EqvGen.trans _ _ _ h h₂))
  · intro h
    exact Relation.EqvGen.trans _ _ _ h₁ (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ h) (Relation.EqvGen.symm _ _ h₂))

/-- Every retained dart lies on one of the two sides of a genuine component split. -/
theorem component_cover_of_split (hc : P.Connected)
    (ht : P.rotation C.right ≠ C.left) (hn : P.edge C.left ≠ C.right)
    (hs : ¬C.split.SameComponent C.left (P.rotation C.right)) (d : C.Dart) :
    C.delete.SameComponent d (C.beforeDart ht) ∨ C.delete.SameComponent d (C.mateDart hn) := by
  obtain h | h := P.vertexCut_component_cover hc C.left (P.rotation C.right) d.val hs
  · right
    apply (C.sameComponent_iff _ _).mpr
    exact Relation.EqvGen.trans _ _ _ h (C.split.component_edge C.left)
  · left
    apply (C.sameComponent_iff _ _).mpr
    have hr : C.split.rotation (P.rotation.symm C.left) = P.rotation C.right :=
      P.vertexCut_rotation_predecessor_left C.left (P.rotation C.right)
    have hh := C.split.component_rotation (P.rotation.symm C.left)
    rw [hr] at hh
    exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ hh)

/-- Each final face is unaffected, or lies on one of the two explicitly affected split faces. -/
theorem face_classification [Finite D] (ht : P.rotation C.right ≠ C.left) (d : C.Dart) :
    (¬P.face.SameCycle d.val (P.rotation.symm C.left) ∧ ¬P.face.SameCycle d.val C.right) ∨
      C.split.face.SameCycle d.val (P.rotation.symm C.left) ∨
        C.split.face.SameCycle d.val C.right := by
  classical
  by_cases ha : P.face.SameCycle d.val (P.rotation.symm C.left)
  · right
    have hh := PermutationCycles.cutAt_affected_cycles P.face (P.rotation.symm C.left) C.right
      (fun he ↦ ht (by
        have he' := congrArg P.rotation he
        rw [Equiv.apply_symm_apply] at he'
        exact he'.symm)) d.val (Or.inl ha)
    have he : C.split.face = PermutationCycles.cutAt P.face (P.rotation.symm C.left) C.right := by
      change (P.vertexCut C.left (P.rotation C.right)).face = _
      simpa only [Equiv.symm_apply_apply] using P.vertexCut_face C.left (P.rotation C.right)
    rw [he]
    exact hh
  · by_cases hb : P.face.SameCycle d.val C.right
    · right
      have hh := PermutationCycles.cutAt_affected_cycles P.face (P.rotation.symm C.left) C.right
        (fun he ↦ ht (by
          have he' := congrArg P.rotation he
          rw [Equiv.apply_symm_apply] at he'
          exact he'.symm)) d.val (Or.inr hb)
      have he : C.split.face = PermutationCycles.cutAt P.face (P.rotation.symm C.left) C.right := by
        change (P.vertexCut C.left (P.rotation C.right)).face = _
        simpa only [Equiv.symm_apply_apply] using P.vertexCut_face C.left (P.rotation C.right)
      rw [he]
      exact hh
    · exact Or.inl ⟨ha, hb⟩

/-- If the two parts of the cut remain joined, deletion retains connectedness. -/
theorem delete_connected_of_nonsplit (hc : P.Connected)
    (hs : C.split.SameComponent C.left (P.rotation C.right)) : C.delete.Connected := by
  intro d e
  apply (C.sameComponent_iff d e).mpr
  exact (P.vertexCut_sameComponent_iff C.left (P.rotation C.right) (hc _ _) hs _ _).mpr
    (hc _ _)

/-- A final face is unaffected, or is one of the two actual surviving affected faces. -/
theorem delete_face_classification [Finite D] (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left ≠ C.right) (d : C.Dart) :
    (¬P.face.SameCycle d.val (P.rotation.symm C.left) ∧ ¬P.face.SameCycle d.val C.right) ∨
      C.delete.face.SameCycle d (C.beforeDart ht) ∨
        C.delete.face.SameCycle d (C.mateDart hn) := by
  rcases C.face_classification ht d with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((C.sameFace_iff _ _).mpr h))
  · right; right
    apply (C.sameFace_iff _ _).mpr
    have hm : C.split.face.SameCycle (P.edge C.left) C.right := by
      have hh : C.split.face.SameCycle (P.edge C.left) (C.split.face (P.edge C.left)) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      simpa only [C.split_face_mate] using hh
    exact h.trans hm.symm

/-- An unaffected face retains its complete cycle relation under the surgery. -/
theorem delete_sameFace_iff_of_unaffected [Finite D] (d e : C.Dart)
    (ha : ¬P.face.SameCycle d.val (P.rotation.symm C.left))
    (hb : ¬P.face.SameCycle d.val C.right) :
    C.delete.face.SameCycle d e ↔ P.face.SameCycle d.val e.val := by
  rw [C.sameFace_iff]
  rw [← C.split.mem_faceBoundary_iff, ← P.mem_faceBoundary_iff]
  have hh := PermutationCycles.cycleBoundary_cutAt_unchanged P.face
    (P.rotation.symm C.left) (P.rotation.symm (P.rotation C.right)) d.val ha
    (by simpa only [Equiv.symm_apply_apply] using hb)
  change e.val ∈ PermutationCycles.cycleBoundary C.split.face d.val ↔ _
  change e.val ∈ PermutationCycles.cycleBoundary (P.vertexCut C.left
    (P.rotation C.right)).face d.val ↔ _
  rw [P.vertexCut_face, hh]
  rfl

/-- In the loop case the second affected split face is a discarded singleton. -/
theorem split_face_right_of_loop (hn : P.edge C.left = C.right) :
    C.split.face C.right = C.right := by
  apply C.split.rotation.injective
  change C.split.rotation (C.split.rotation.symm (P.edge C.right)) =
    C.split.rotation C.right
  rw [Equiv.apply_symm_apply, C.split_rotation_right, ← hn, P.edge_involutive]

/-- The other face of the isolated split loop is a discarded singleton as well. -/
theorem split_face_left_of_loop (hn : P.edge C.left = C.right) :
    C.split.face C.left = C.left := by
  apply C.split.rotation.injective
  change C.split.rotation (C.split.rotation.symm (P.edge C.left)) =
    C.split.rotation C.left
  rw [Equiv.apply_symm_apply, C.split_rotation_left, hn]

/-- Only one affected face survives cancellation of an adjacent loop. -/
theorem delete_face_classification_of_loop [Finite D] (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left = C.right) (d : C.Dart) :
    (¬P.face.SameCycle d.val (P.rotation.symm C.left) ∧ ¬P.face.SameCycle d.val C.right) ∨
      C.delete.face.SameCycle d (C.beforeDart ht) := by
  rcases C.face_classification ht d with h | h | h
  · exact Or.inl h
  · exact Or.inr ((C.sameFace_iff _ _).mpr h)
  · exact (d.property.2 (h.eq_of_right (C.split_face_right_of_loop hn))).elim

/-- In a spherical map, splitting one affected face separates its two retained sides. -/
theorem delete_regions_separated [Fintype D] (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left ≠ C.right) (hE : P.EulerEquality)
    (hf : P.face.SameCycle (P.rotation.symm C.left) C.right) :
    ¬C.delete.SameComponent (C.beforeDart ht) (C.mateDart hn) :=
  (C.separated_regions_iff ht hn).mpr ((C.split_components_iff_same_face ht hE).mpr hf)

/-- Merging distinct affected faces leaves a connected map connected. -/
theorem delete_connected_of_distinct_faces [Finite D] (hc : P.Connected)
    (hf : ¬P.face.SameCycle (P.rotation.symm C.left) C.right) : C.delete.Connected := by
  apply C.delete_connected_of_nonsplit hc
  by_contra hs
  have hh := P.vertexCut_face_sameCycle_of_split C.left (P.rotation C.right) hs
  exact hf (by simpa only [Equiv.symm_apply_apply] using hh)

/-- Deleting an entire two-corner vertex also retains connectedness. -/
theorem delete_connected_of_two_cycle (hc : P.Connected)
    (ht : P.rotation C.right = C.left) : C.delete.Connected := by
  intro d e
  exact (C.sameComponent_iff_of_two_cycle ht d e).mpr (hc _ _)

/-- If the old affected faces were distinct, their surviving representatives share the
single merged final face. -/
theorem delete_affected_faces_sameCycle [Finite D] (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left ≠ C.right)
    (hf : ¬P.face.SameCycle (P.rotation.symm C.left) C.right) :
    C.delete.face.SameCycle (C.beforeDart ht) (C.mateDart hn) := by
  apply (C.sameFace_iff _ _).mpr
  have hh := PermutationCycles.cutAt_sameCycle_of_not_sameCycle P.face
    (P.rotation.symm C.left) C.right hf
  have he : C.split.face = PermutationCycles.cutAt P.face
      (P.rotation.symm C.left) C.right := by
    simpa only [split, Equiv.symm_apply_apply] using
      P.vertexCut_face C.left (P.rotation C.right)
  rw [← he] at hh
  have hm : C.split.face.SameCycle (P.edge C.left) C.right := by
    have hstep : C.split.face.SameCycle (P.edge C.left) (C.split.face (P.edge C.left)) :=
      Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    simpa only [C.split_face_mate] using hstep
  exact hh.trans hm.symm

/-- An adjacent loop cut separates the two original affected face positions from one
old face, provided there is a surviving part of the vertex. -/
theorem affected_sameFace_of_loop [Finite D] (ht : P.rotation C.right ≠ C.left)
    (hn : P.edge C.left = C.right) :
    P.face.SameCycle (P.rotation.symm C.left) C.right := by
  have hneq : ¬C.split.face.SameCycle (P.rotation.symm C.left) C.right := by
    intro h
    exact (C.beforeDart ht).property.2 (h.eq_of_right (C.split_face_right_of_loop hn))
  have hh := PermutationCycles.cutAt_sameCycle_of_not_sameCycle C.split.face
    (P.rotation.symm C.left) C.right hneq
  have he : C.split.face = PermutationCycles.cutAt P.face
      (P.rotation.symm C.left) C.right := by
    simpa only [split, Equiv.symm_apply_apply] using
      P.vertexCut_face C.left (P.rotation C.right)
  rw [he, PermutationCycles.cutAt_cutAt] at hh
  exact hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
