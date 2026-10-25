module

public import SmallPresentation.SmallCancellationGeometryCornerCancellationFaces
public import SmallPresentation.SmallCancellationGeometryCornerCancellationCycles

/-! Actual component locations under adjacent-corner surgery. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace DegreeTwoVertex

variable {D : Type*} {P : RibbonMap D} (C : DegreeTwoVertex P)

/-- Inclusion preserves and reflects components under a nonisolated degree-two suppression. -/
theorem sameComponent_iff (d e : C.Dart) :
    C.suppress.SameComponent d e ↔ P.SameComponent d.val e.val := by
  have hu : C.suppress.SameComponent d e ↔ C.dualBigon.suppress.SameComponent d e := by
    have hh := C.dualBigon.suppress.undual.dual_sameComponent_iff d e
    rw [RibbonMap.undual_dual] at hh
    exact hh.symm
  rw [hu]
  constructor
  · intro h
    exact (P.dual_sameComponent_iff _ _).mp (C.dualBigon.include_sameComponent h)
  · intro h
    have hh := C.dualBigon.collapse_sameComponent ((P.dual_sameComponent_iff _ _).mpr h)
    simpa only [Bigon.collapse_survivor] using hh

end DegreeTwoVertex

namespace AdjacentCancellation

variable {D : Type*} {P : RibbonMap D} (C : AdjacentCancellation P)

/-- Component splitting occurs only at the preliminary cut. Removing the pair preserves
and reflects the actual component relation of all surviving incidences. -/
theorem sameComponent_iff (d e : C.Dart) :
    C.delete.SameComponent d e ↔ C.split.SameComponent d.val e.val := by
  classical
  by_cases hn : P.edge C.left = C.right
  · have hh := C.reconnected.restrict_sameComponent_iff
      (fun d ↦ d ≠ C.left ∧ d ≠ C.right) C.edge_survives C.rotation_survives d e
    change C.delete.SameComponent d e ↔ C.reconnected.SameComponent d.val e.val at hh
    rw [C.reconnected_eq_of_loop hn] at hh
    exact hh
  · let A := C.degreeTwo hn
    let f : A.Dart ≃ C.Dart := A.dartEquiv
    have hh := A.suppress.relabel_component_iff C.delete f
      (C.degreeTwo_edge_conjugacy hn) (C.degreeTwo_rotation_conjugacy hn) (f.symm d) (f.symm e)
    rw [f.apply_symm_apply d, f.apply_symm_apply e] at hh
    exact hh.symm.trans (A.sameComponent_iff (f.symm d) (f.symm e))

/-- Every surviving component remains within its original component before cancellation. -/
theorem component_projects (d e : C.Dart) (h : C.delete.SameComponent d e) :
    P.SameComponent d.val e.val := by
  have hc : P.SameComponent C.left (P.rotation C.right) :=
    Relation.EqvGen.trans _ _ _ (by
      change P.SameComponent C.left C.right
      have hh := P.component_rotation C.left
      rw [C.next] at hh
      exact hh) (P.component_rotation C.right)
  exact P.vertexCut_component_refines _ _ hc ((C.sameComponent_iff d e).mp h)

/-- If the pair was already the whole vertex, no preliminary component split occurs. -/
theorem sameComponent_iff_of_two_cycle (ht : P.rotation C.right = C.left) (d e : C.Dart) :
    C.delete.SameComponent d e ↔ P.SameComponent d.val e.val := by
  rw [C.sameComponent_iff, C.split_eq_of_two_cycle ht]

end AdjacentCancellation
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
