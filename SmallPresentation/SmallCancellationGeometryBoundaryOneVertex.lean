module

public import SmallPresentation.SmallCancellationGeometryBoundaryProducts
public import SmallPresentation.SmallCancellationGeometryEdgeContractionTopology

/-!
# The nonabelian boundary theorem for a spherical one-vertex ribbon

Euler counting gives an actual one-corner face. Its edge ends are adjacent inverse
letters, so deleting them preserves the complete boundary product. Induction on the
actual number of darts proves the word is trivial in every group.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

universe u
variable {K : Type*} [Group K]

/-- Every inverse-edge labelling of a spherical one-vertex ribbon has trivial vertex product. -/
theorem one_vertex_product_one (D : Type u) [Fintype D] (P : RibbonMap D) (w : D → K)
    (he : ∀ d, w (P.edge d) = (w d)⁻¹)
    (hv : ∀ d e, P.rotation.SameCycle d e) (hE : P.EulerEquality) (d : D) :
    ((P.vertexBoundary d).map w).prod = 1 := by
  classical
  obtain ⟨a, ha⟩ := P.exists_adjacent_mates_of_one_vertex d hv hE
  let C : AdjacentCancellation P := ⟨a, P.edge a, (P.edge_ne a).symm, ha⟩
  have hinv : w C.left * w C.right = 1 := by
    change w a * w (P.edge a) = 1
    rw [he, mul_inv_cancel]
  by_cases hn : Nonempty C.Dart
  · let e := Classical.choice hn
    have hnew : ((C.delete.vertexBoundary e).map (fun x ↦ w x.val)).prod = 1 := by
      apply one_vertex_product_one C.Dart C.delete (fun x ↦ w x.val) ?_ ?_ (C.delete_euler hE) e
      · intro x
        have hh := C.reconnected_eq_of_loop (show P.edge C.left = C.right from rfl)
        change w (C.reconnected.edge x.val) = (w x.val)⁻¹
        rw [hh]
        exact he x.val
      · intro x y
        exact (C.sameVertex_iff x y).mpr (hv x.val y.val)
    rw [C.vertex_product w hinv e] at hnew
    exact (cycleProduct_eq_one_of_sameCycle P.rotation w (hv d e.val)).mpr hnew
  · have only (x : D) : x = C.left ∨ x = C.right := by
      by_contra hx
      push Not at hx
      exact hn ⟨⟨x, hx⟩⟩
    have hr : P.rotation C.right = C.left := by
      rcases only (P.rotation C.right) with h | h
      · exact h
      · exact False.elim (C.ne (P.rotation.injective (C.next.trans h.symm)))
    have hbase : ((P.vertexBoundary C.left).map w).prod = 1 :=
      (C.pair_vertex_product w hr).trans hinv
    exact (cycleProduct_eq_one_of_sameCycle P.rotation w (hv d C.left)).mpr hbase
termination_by Fintype.card D
decreasing_by
  exact C.card_darts_lt

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
