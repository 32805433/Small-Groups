module

public import SmallPresentation.SmallCancellationGeometryComponents
public import SmallPresentation.PermutationCycleCut

/-!
# Actual vertex cuts and their effect on face permutations and components

A cut switches two incoming arrows of the vertex rotation, leaving every edge unchanged.
The face permutation is computed exactly. Explicit interval coordinates prove that the
operation adds one vertex. Components are treated separately: a cut can split a component;
an equivalence of components is proved only when the cut points remain connected afterward.
No sphere Euler equation or connectedness-preservation assumption is hidden in the operation.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles
attribute [local instance] Classical.propDecidable

variable {D E : Type*} (P : RibbonMap D)

/-- Cut a vertex rotation at two incoming arrows, preserving all edge incidences. -/
noncomputable def vertexCut (a b : D) : RibbonMap D where
  edge := P.edge
  edge_involutive := P.edge_involutive
  edge_ne := P.edge_ne
  rotation := cutAt P.rotation a b

@[simp] theorem vertexCut_edge (a b : D) : (P.vertexCut a b).edge = P.edge := rfl

@[simp] theorem vertexCut_rotation (a b : D) :
    (P.vertexCut a b).rotation = cutAt P.rotation a b := rfl

/-- Repeating the cut reconnects the original vertex rotation. -/
theorem vertexCut_twice (a b : D) : (P.vertexCut a b).vertexCut a b = P := by
  apply RibbonMap.ext
  · rfl
  · exact cutAt_cutAt P.rotation a b

/-- The face surgery is the corresponding switch at the two predecessor corners. -/
theorem vertexCut_face (a b : D) :
    (P.vertexCut a b).face = cutAt P.face (P.rotation.symm a) (P.rotation.symm b) := by
  classical
  apply Equiv.ext
  intro d
  change (cutAt P.rotation a b).symm (P.edge d) = _
  simp only [cutAt, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_swap, face_apply]
  exact P.rotation.symm.injective.map_swap a b (P.edge d)

/-- The unchanged edge permutation gives exactly the unchanged edge quotient. -/
def vertexCutEdgeEquiv (a b : D) : (P.vertexCut a b).Edge ≃ P.Edge := Equiv.refl _

/-- A cut through two nonempty consecutive intervals adds exactly one actual vertex. -/
theorem vertexCut_card_vertices [Finite D] [Finite E]
    (τ : Equiv.Perm E) (m n : ℕ) (e : Fin ((m + 1) + (n + 1)) ⊕ E ≃ D)
    (he : ∀ d, e (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ d) = P.rotation (e d))
    [Fintype P.Vertex]
    [Fintype (P.vertexCut (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n)))).Vertex] :
    Fintype.card (P.vertexCut (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n)))).Vertex = Fintype.card P.Vertex + 1 := by
  let : Fintype (Cycles (cutAt P.rotation (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n))))) :=
    inferInstanceAs (Fintype (P.vertexCut (e (Sum.inl (intervalStartLeft m n)))
      (e (Sum.inl (intervalStartRight m n)))).Vertex)
  exact card_cutAt_of_intervalCoordinates P.rotation τ m n e he

/-- If the predecessor corners lie on one explicitly indexed face cycle, the same
operation splits that face into exactly two cycles. This allows component splitting;
no preservation of the total Euler characteristic is asserted. -/
theorem vertexCut_card_faces [Finite D] [Finite E]
    (τ : Equiv.Perm E) (m n : ℕ) (e : Fin ((m + 1) + (n + 1)) ⊕ E ≃ D)
    (he : ∀ d, e (Equiv.sumCongr (finRotate ((m + 1) + (n + 1))) τ d) = P.face (e d))
    [Fintype P.Face]
    [Fintype (P.vertexCut (P.rotation (e (Sum.inl (intervalStartLeft m n))))
      (P.rotation (e (Sum.inl (intervalStartRight m n))))).Face] :
    Fintype.card (P.vertexCut (P.rotation (e (Sum.inl (intervalStartLeft m n))))
      (P.rotation (e (Sum.inl (intervalStartRight m n))))).Face = Fintype.card P.Face + 1 := by
  classical
  let κ := cutAt P.face (e (Sum.inl (intervalStartLeft m n)))
    (e (Sum.inl (intervalStartRight m n)))
  let := Fintype.ofFinite (Cycles κ)
  have hface : (P.vertexCut (P.rotation (e (Sum.inl (intervalStartLeft m n))))
      (P.rotation (e (Sum.inl (intervalStartRight m n))))).face = κ := by
    rw [vertexCut_face, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hc := Fintype.card_congr (Equiv.cast (congrArg Cycles hface))
  have hsplit := card_cutAt_of_intervalCoordinates P.face τ m n e he
  exact hc.trans hsplit

/-- Switching two points already in a component sends each point to that same component. -/
theorem component_swap (a b : D) (hab : P.SameComponent a b) (d : D) :
    P.SameComponent d (Equiv.swap a b d) := by
  classical
  by_cases ha : d = a
  · subst d
    rw [Equiv.swap_apply_left]
    exact hab
  · by_cases hb : d = b
    · subst d
      rw [Equiv.swap_apply_right]
      exact Relation.EqvGen.symm _ _ hab
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
      exact Relation.EqvGen.refl _

/-- Cutting within an old component can separate it, but cannot join previously distinct ones. -/
theorem vertexCut_component_refines (a b : D) (hab : P.SameComponent a b)
    {d e : D} (h : (P.vertexCut a b).SameComponent d e) : P.SameComponent d e := by
  apply (P.vertexCut a b).map_components P id ?_ ?_ h
  · exact P.component_edge
  · intro d
    exact Relation.EqvGen.trans _ _ _ (P.component_rotation d)
      (P.component_swap a b hab (P.rotation d))

/-- If an alternate path still joins the cut points, no connected component is split. -/
theorem vertexCut_sameComponent_iff (a b : D) (hold : P.SameComponent a b)
    (hnew : (P.vertexCut a b).SameComponent a b) (d e : D) :
    (P.vertexCut a b).SameComponent d e ↔ P.SameComponent d e := by
  constructor
  · exact P.vertexCut_component_refines a b hold
  · have hh := (P.vertexCut a b).vertexCut_component_refines a b hnew (d := d) (e := e)
    simpa only [vertexCut_twice] using hh

/-- Component preservation follows from an actual alternate path, not merely from the vertex cut. -/
noncomputable def vertexCutComponentsEquiv (a b : D) (hold : P.SameComponent a b)
    (hnew : (P.vertexCut a b).SameComponent a b) :
    (P.vertexCut a b).Component ≃ P.Component :=
  Quotient.congr (Equiv.refl _) (fun d e ↦ P.vertexCut_sameComponent_iff a b hold hnew d e)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
