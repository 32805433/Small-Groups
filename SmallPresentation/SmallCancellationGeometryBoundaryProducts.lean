module

public import SmallPresentation.PermutationCycleProducts
public import SmallPresentation.SmallCancellationGeometryRelativeCornerWords

/-! Ordered group products under cancellation of adjacent inverse incidences. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace AdjacentCancellation

variable {D K : Type*} [Finite D] [Group K] {P : RibbonMap D}
    (C : AdjacentCancellation P) (w : D → K)

/-- Removing consecutive inverse labels preserves the exact based product on every survivor. -/
theorem vertex_product (hinv : w C.left * w C.right = 1) (d : C.Dart) :
    (((C.delete.vertexBoundary d).map (fun e ↦ w e.val)).prod) =
      ((P.vertexBoundary d.val).map w).prod := by
  classical
  have hh := congrArg List.prod (C.vertex_blocks (fun e ↦ [w e]) d)
  simp only [List.flatMap_def, List.prod_flatten, List.map_map, Function.comp_def,
    List.prod_cons, List.prod_nil, mul_one] at hh
  rw [← hh]
  apply congrArg List.prod
  apply List.map_congr_left
  intro e _
  by_cases he : P.rotation e.val = C.left
  · simp [blocks, he, hinv]
  · simp [blocks, he]

omit [Finite D] in
/-- A whole two-incidence vertex reads its two labels in the specified order. -/
theorem pair_vertex_product (hr : P.rotation C.right = C.left) :
    ((P.vertexBoundary C.left).map w).prod = w C.left * w C.right := by
  have hw : PermutationCycles.Walk P.rotation C.left C.left [C.left, C.right] := by
    apply PermutationCycles.Walk.cons
    rw [C.next]
    apply PermutationCycles.Walk.cons
    rw [hr]
    exact .nil _
  have hl := hw.eq_cycleBoundary (by simp) (by simp [C.ne])
  change ((PermutationCycles.cycleBoundary P.rotation C.left).map w).prod = _
  rw [← hl]
  simp

end AdjacentCancellation
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
