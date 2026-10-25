module

public import SmallPresentation.SmallCancellationGeometryCornerCancellationCounts
public import SmallPresentation.SmallCancellationDipoleSplice

/-!
# Contraction of an actual edge joining distinct vertices

First splice the endpoint cycles along the chosen edge. Its two inverse incidences
then become consecutive, and adjacent-corner cancellation removes them. This gives
an explicit finite surgery preserving spherical Euler characteristic. When the
whole component consists of the single edge, its empty residual vertex disappears,
as required by the dart-defined cell convention.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

attribute [local instance] Classical.propDecidable

variable {D : Type*} [Finite D] (P : RibbonMap D) (a : D)

/-- The spliced joining edge is an actual adjacent pair. -/
noncomputable def spliceCancellation : AdjacentCancellation (P.edgeSplice a) where
  left := a
  right := P.edge a
  ne := (P.edge_ne a).symm
  next := by
    classical
    change Equiv.swap (P.rotation a) (P.edge a) (P.rotation a) = P.edge a
    exact Equiv.swap_apply_left _ _

/-- Retain precisely the old incidences outside the contracted edge. -/
abbrev ContractDart := {d : D // d ≠ a ∧ d ≠ P.edge a}

/-- Actual edge contraction, with both old endpoints removed. -/
noncomputable def contractEdge : RibbonMap (P.ContractDart a) := (P.spliceCancellation a).delete

/-- Contracting an edge between distinct vertices preserves the spherical Euler equation. -/
theorem contractEdge_euler [Fintype D] (hn : ¬P.rotation.SameCycle a (P.edge a))
    (h : P.EulerEquality) : (P.contractEdge a).EulerEquality :=
  (P.spliceCancellation a).delete_euler ((P.edgeSplice_euler_iff a hn).mpr h)

omit [Finite D] in
/-- Contraction removes exactly the two incidences of the chosen edge. -/
theorem contractEdge_card_darts [Fintype D] :
    Fintype.card D = Fintype.card (P.ContractDart a) + 2 := by
  classical
  exact (P.spliceCancellation a).card_darts

theorem contractEdge_card_edges [Fintype D] :
    Fintype.card P.Edge = Fintype.card (P.contractEdge a).Edge + 1 :=
  (P.spliceCancellation a).card_edges

omit [Finite D] in
/-- All surviving edge pairings are literally unchanged. -/
theorem contractEdge_edge_val (d : P.ContractDart a) :
    ((P.contractEdge a).edge d).val = P.edge d.val := by
  classical
  have he : (P.edgeSplice a).edge a = P.edge a := rfl
  have hr := (P.spliceCancellation a).reconnected_eq_of_loop he
  change ((P.spliceCancellation a).reconnected.edge d.val) = P.edge d.val
  rw [hr]
  rfl

omit [Finite D] in
open Classical in
/-- The exact contracted successor bypasses both ends in the spliced cyclic order. -/
theorem contractEdge_rotation_val (d : P.ContractDart a) :
    ((P.contractEdge a).rotation d).val =
      if (P.edgeSplice a).rotation d.val = a then (P.edgeSplice a).rotation (P.edge a)
      else (P.edgeSplice a).rotation d.val :=
  (P.spliceCancellation a).rotation_val d

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
