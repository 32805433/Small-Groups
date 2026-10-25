module

public import SmallPresentation.SmallCancellationGeometryCorridorCycleCuts
public import SmallPresentation.SmallCancellationGeometryCorridorComponents
public import SmallPresentation.SmallCancellationGeometryEuler

/-!
# Coupled face and component changes of actual corridor cuts

Splitting a component forces the two predecessor corners to lie on one old face.
Consequently a component split adds one face as well as one vertex. This is the
finite permutation separation statement required in the Euler-preservation proof.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D : Type*} [Finite D] (P : RibbonMap D) (a b : D)

omit [Finite D] in
theorem vertexCut_rotation_predecessor_left :
    (P.vertexCut a b).rotation (P.rotation.symm a) = b := by
  classical
  simp only [vertexCut_rotation, cutAt_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left]

omit [Finite D] in
theorem vertexCut_rotation_predecessor_right :
    (P.vertexCut a b).rotation (P.rotation.symm b) = a := by
  classical
  simp only [vertexCut_rotation, cutAt_apply, Equiv.apply_symm_apply, Equiv.swap_apply_right]

/-- A disconnected cut cannot have merged two formerly distinct face cycles. -/
theorem vertexCut_face_sameCycle_of_split
    (hsplit : ¬(P.vertexCut a b).SameComponent a b) :
    P.face.SameCycle (P.rotation.symm a) (P.rotation.symm b) := by
  by_contra hh
  have hf := cutAt_sameCycle_of_not_sameCycle P.face (P.rotation.symm a)
    (P.rotation.symm b) hh
  rw [← P.vertexCut_face a b] at hf
  have hc := (P.vertexCut a b).component_of_faceCycle hf
  have ha := (P.vertexCut a b).component_rotation (P.rotation.symm a)
  have hb := (P.vertexCut a b).component_rotation (P.rotation.symm b)
  rw [P.vertexCut_rotation_predecessor_left] at ha
  rw [P.vertexCut_rotation_predecessor_right] at hb
  exact hsplit (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hb)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hc) ha))

/-- A genuine split of an actual vertex adds exactly one actual vertex. -/
theorem vertexCut_card_vertices_of_sameCycle (hne : a ≠ b)
    (hcycle : P.rotation.SameCycle a b) :
    Fintype.card (P.vertexCut a b).Vertex = Fintype.card P.Vertex + 1 := by
  let := Fintype.ofFinite (Cycles (cutAt P.rotation a b))
  exact card_cutAt_of_sameCycle P.rotation a b hne hcycle

/-- Splitting a component also splits its affected face. -/
theorem vertexCut_card_faces_of_split (hne : a ≠ b)
    (hsplit : ¬(P.vertexCut a b).SameComponent a b) :
    Fintype.card (P.vertexCut a b).Face = Fintype.card P.Face + 1 := by
  let := Fintype.ofFinite (Cycles (cutAt P.face (P.rotation.symm a) (P.rotation.symm b)))
  have he := Fintype.card_congr (Equiv.cast (congrArg Cycles (P.vertexCut_face a b)))
  have hf := card_cutAt_of_sameCycle P.face (P.rotation.symm a) (P.rotation.symm b)
    (P.rotation.symm.injective.ne hne) (P.vertexCut_face_sameCycle_of_split a b hsplit)
  exact he.trans hf

/-- Every genuine vertex cut changes the face count by exactly one, in one direction. -/
theorem vertexCut_card_faces_cases (hne : a ≠ b) :
    Fintype.card (P.vertexCut a b).Face = Fintype.card P.Face + 1 ∨
      Fintype.card P.Face = Fintype.card (P.vertexCut a b).Face + 1 := by
  let := Fintype.ofFinite (Cycles (cutAt P.face (P.rotation.symm a) (P.rotation.symm b)))
  have he := Fintype.card_congr (Equiv.cast (congrArg Cycles (P.vertexCut_face a b)))
  have hf := card_cutAt_cases P.face (P.rotation.symm a) (P.rotation.symm b)
    (P.rotation.symm.injective.ne hne)
  rcases hf with hf | hf
  · exact Or.inl (he.trans hf)
  · exact Or.inr (hf.trans (congrArg (fun n ↦ n + 1) he.symm))

/-- Euler planarity is preserved by splitting any actual vertex into two cyclic intervals.
The component-splitting case is included rather than ruled out by hypothesis. -/
theorem vertexCut_preserves_euler [Fintype D] (hne : a ≠ b)
    (hcycle : P.rotation.SameCycle a b)
    (hplanar : Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) :
    Fintype.card (P.vertexCut a b).Vertex + Fintype.card (P.vertexCut a b).Face =
      Fintype.card (P.vertexCut a b).Edge +
        2 * Fintype.card (P.vertexCut a b).Component := by
  classical
  have hv := P.vertexCut_card_vertices_of_sameCycle a b hne hcycle
  have he := Fintype.card_congr (P.vertexCutEdgeEquiv a b)
  have hold := P.component_of_vertexCycle hcycle
  by_cases hn : (P.vertexCut a b).SameComponent a b
  · have hc := Fintype.card_congr (P.vertexCutComponentsEquiv a b hold hn)
    have hu := (P.vertexCut a b).euler_upper_bound
    have hf := P.vertexCut_card_faces_cases a b hne
    omega
  · have hc := P.vertexCut_card_components_split a b hold hn
    have hf := P.vertexCut_card_faces_of_split a b hne hn
    change Fintype.card (P.vertexCut a b).Component = Fintype.card P.Component + 1 at hc
    omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
