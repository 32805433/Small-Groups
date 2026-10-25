module

public import SmallPresentation.SmallCancellationDipoleRibbon
public import SmallPresentation.SmallCancellationGeometryCorridorRefinement

/-!
# Splicing two distinct vertices along an actual joining edge

Switching the incoming arrows at the successor of one edge end and the other end merges
the two vertices and creates one face. The actual component set is unchanged. This is the
first planar surgery in a full-row dipole deletion, proved without a topological assumption
on the result of the surgery.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D : Type*} [Finite D] (P : RibbonMap D) (a : D)

/-- Merge the endpoint vertices at an actual edge, retaining every dart and every edge. -/
noncomputable def edgeSplice : RibbonMap D := P.vertexCut (P.rotation a) (P.edge a)

theorem edgeSplice_counts (hn : ¬P.rotation.SameCycle a (P.edge a)) :
    Fintype.card P.Vertex = Fintype.card (P.edgeSplice a).Vertex + 1 ∧
    Fintype.card (P.edgeSplice a).Face = Fintype.card P.Face + 1 ∧
    Fintype.card (P.edgeSplice a).Edge = Fintype.card P.Edge ∧
    Fintype.card (P.edgeSplice a).Component = Fintype.card P.Component := by
  have hnc : ¬P.rotation.SameCycle (P.rotation a) (P.edge a) := by
    simpa only [Equiv.Perm.sameCycle_apply_left] using hn
  have hne : P.rotation a ≠ P.edge a := by
    intro he
    exact hnc (he ▸ Equiv.Perm.SameCycle.refl _ _)
  have hold : P.SameComponent (P.rotation a) (P.edge a) :=
    Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (P.component_rotation a))
      (P.component_edge a)
  have hnew : (P.edgeSplice a).SameComponent (P.rotation a) (P.edge a) :=
    (P.edgeSplice a).component_of_vertexCycle
      (cutAt_sameCycle_of_not_sameCycle P.rotation (P.rotation a) (P.edge a) hnc)
  have hv : Fintype.card P.Vertex = Fintype.card (P.edgeSplice a).Vertex + 1 := by
    let := Fintype.ofFinite (Cycles (cutAt P.rotation (P.rotation a) (P.edge a)))
    exact card_cutAt_of_not_sameCycle P.rotation (P.rotation a) (P.edge a) hnc
  have hf : Fintype.card (P.edgeSplice a).Face = Fintype.card P.Face + 1 := by
    let := Fintype.ofFinite (Cycles (cutAt P.face (P.rotation.symm (P.rotation a))
      (P.rotation.symm (P.edge a))))
    have he := Fintype.card_congr (Equiv.cast (congrArg Cycles
      (P.vertexCut_face (P.rotation a) (P.edge a))))
    have hc : P.face.SameCycle (P.rotation.symm (P.rotation a))
        (P.rotation.symm (P.edge a)) := by
      rw [Equiv.symm_apply_apply]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact he.trans (card_cutAt_of_sameCycle P.face _ _
      (P.rotation.symm.injective.ne hne) hc)
  exact ⟨hv, hf, Fintype.card_congr (P.vertexCutEdgeEquiv _ _),
    Fintype.card_congr (P.vertexCutComponentsEquiv _ _ hold hnew)⟩

theorem edgeSplice_euler_iff (hn : ¬P.rotation.SameCycle a (P.edge a)) :
    (Fintype.card (P.edgeSplice a).Vertex + Fintype.card (P.edgeSplice a).Face =
      Fintype.card (P.edgeSplice a).Edge + 2 * Fintype.card (P.edgeSplice a).Component) ↔
    (Fintype.card P.Vertex + Fintype.card P.Face =
      Fintype.card P.Edge + 2 * Fintype.card P.Component) := by
  obtain ⟨hv, hf, he, hc⟩ := P.edgeSplice_counts a hn
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon

variable {O X Q : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} (P : BasedRowRibbon words q)

theorem rotation_iterate_occurrence (d : RowDarts words) (n : ℕ) :
    (P.map.rotation^[n] d).1 = d.1 := by
  have hf (e : RowDarts words) : (P.map.rotation e).1 = e.1 := by
    rw [P.rotation_eq]
    rcases e with ⟨o, e⟩
    rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hf _).trans ih

theorem occurrence_eq_of_sameVertex [Finite O] {d e : RowDarts words}
    (h : P.map.rotation.SameCycle d e) : d.1 = e.1 := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  have he := congrArg Sigma.fst hn
  rw [Equiv.Perm.coe_pow, P.rotation_iterate_occurrence] at he
  exact he

namespace Dipole

variable {P} (D : P.Dipole)

theorem anchor_distinct_vertices [Finite O] :
    ¬P.map.rotation.SameCycle ⟨D.first, D.anchor⟩
      (P.map.edge ⟨D.first, D.anchor⟩) := by
  rw [D.edge_anchor]
  exact fun h ↦ D.distinct (P.occurrence_eq_of_sameVertex h)

theorem splice_euler_iff [Finite O] :
    (Fintype.card (P.map.edgeSplice ⟨D.first, D.anchor⟩).Vertex +
        Fintype.card (P.map.edgeSplice ⟨D.first, D.anchor⟩).Face =
      Fintype.card (P.map.edgeSplice ⟨D.first, D.anchor⟩).Edge +
        2 * Fintype.card (P.map.edgeSplice ⟨D.first, D.anchor⟩).Component) ↔
    (Fintype.card P.map.Vertex + Fintype.card P.map.Face =
      Fintype.card P.map.Edge + 2 * Fintype.card P.map.Component) :=
  P.map.edgeSplice_euler_iff _ D.anchor_distinct_vertices

end Dipole
end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon
