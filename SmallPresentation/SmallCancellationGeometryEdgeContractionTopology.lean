module

public import SmallPresentation.SmallCancellationGeometryCorridorMergeCycles
public import SmallPresentation.SmallCancellationGeometryEdgeContraction
public import SmallPresentation.SmallCancellationGeometryCornerCancellationCycles

/-! Connectivity and the one-vertex terminal case of planar edge contraction. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} [Finite D] (P : RibbonMap D)

theorem contractEdge_connected (hc : P.Connected) (a : D)
    (hn : ¬P.rotation.SameCycle a (P.edge a)) : (P.contractEdge a).Connected := by
  have hp := P.card_components_of_connected hc a
  have hs := (P.edgeSplice_counts a hn).2.2.2
  have hsub : Subsingleton (P.edgeSplice a).Component :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  have hconn : (P.edgeSplice a).Connected := by
    intro d e
    exact Quotient.exact (hsub.elim ((P.edgeSplice a).componentClass d)
      ((P.edgeSplice a).componentClass e))
  exact (P.spliceCancellation a).delete_connected_of_loop hconn rfl

theorem contractEdge_sameVertex_iff (a : D) (d e : P.ContractDart a) :
    (P.contractEdge a).rotation.SameCycle d e ↔
      (P.edgeSplice a).rotation.SameCycle d.val e.val :=
  (P.spliceCancellation a).sameVertex_iff d e

/-- The splicing operation merges precisely the two endpoint vertices. -/
theorem edgeSplice_sameVertex_iff (a : D)
    (hn : ¬P.rotation.SameCycle a (P.edge a)) (d e : D) :
    (P.edgeSplice a).rotation.SameCycle d e ↔
      P.rotation.SameCycle d e ∨
        (P.rotation.SameCycle d a ∨ P.rotation.SameCycle d (P.edge a)) ∧
          (P.rotation.SameCycle e a ∨ P.rotation.SameCycle e (P.edge a)) := by
  have hh := PermutationCycles.sameCycle_cutAt_merge_iff P.rotation
    (P.rotation a) (P.edge a)
    (by simpa only [Equiv.Perm.sameCycle_apply_left] using hn) d e
  change (PermutationCycles.cutAt P.rotation (P.rotation a) (P.edge a)).SameCycle d e ↔ _
  simpa only [Equiv.Perm.sameCycle_apply_right] using hh

omit [Finite D] in
/-- If every edge is a loop, connectedness implies that all incidences belong to one vertex. -/
theorem all_sameVertex_of_edges_loops (hc : P.Connected)
    (hl : ∀ d, P.rotation.SameCycle d (P.edge d)) (d e : D) :
    P.rotation.SameCycle d e := by
  have hh := hc d e
  induction hh with
  | rel x y h =>
    rcases h with h | h
    · rw [← h]
      exact hl x
    · rw [← h]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  | refl x => exact .refl _ _
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A nonempty spherical one-vertex ribbon has an actual singleton face, hence a consecutive
inverse edge pair. This is the terminal cancellation step in the planar boundary argument. -/
theorem exists_adjacent_mates_of_one_vertex [Fintype D] (a : D)
    (hv : ∀ d e, P.rotation.SameCycle d e) (hE : P.EulerEquality) :
    ∃ d, P.rotation d = P.edge d := by
  classical
  have hvc : Fintype.card P.Vertex = 1 := by
    let : Unique P.Vertex := {
      default := P.vertexOf a
      uniq := fun c ↦ Quotient.inductionOn c (fun d ↦ Quotient.sound (hv d a)) }
    exact Fintype.card_unique
  have hc : P.Connected := fun d e ↦ P.component_of_vertexCycle (hv d e)
  have hcc := P.card_components_of_connected hc a
  by_contra hn
  push Not at hn
  have hface (d : D) : 2 ≤ (P.faceBoundary d).length := by
    have hp := P.faceBoundary_nonempty d
    have hpos : 0 < (P.faceBoundary d).length := List.length_pos_iff.mpr hp
    have hne : (P.faceBoundary d).length ≠ 1 := by
      intro he
      have hperiod : Function.minimalPeriod P.face d = 1 := by
        simpa only [faceBoundary, List.length_ofFn] using he
      have hf := Function.minimalPeriod_eq_one_iff_isFixedPt.mp hperiod
      apply hn d
      have hh := congrArg P.rotation hf
      simpa only [face_apply, Equiv.apply_symm_apply] using hh.symm
    omega
  have hbound : 2 * Fintype.card P.Face ≤ Fintype.card D := by
    apply incidence_lower_bound P.faceOf 2
    intro f
    induction f using Quotient.inductionOn with
    | h d =>
      change 2 ≤ incidenceDegree P.faceOf (P.faceOf d)
      rw [P.face_incidenceDegree]
      exact hface d
  have hd := P.card_darts
  change Fintype.card P.Vertex + Fintype.card P.Face =
    Fintype.card P.Edge + 2 * Fintype.card P.Component at hE
  omega

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
