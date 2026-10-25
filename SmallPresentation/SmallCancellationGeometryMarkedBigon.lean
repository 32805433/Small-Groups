module

public import SmallPresentation.SmallCancellationGeometryMarkedBands
public import SmallPresentation.SmallCancellationGeometryRelativeReduction

/-! Actual marked-vertex membership under bigon compression. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

variable {D : Type*} [Finite D] (P : RibbonMap D)

/-- The length of a based vertex boundary is independent of its chosen starting dart. -/
theorem vertexBoundary_length_eq_of_sameCycle {a b : D} (h : P.rotation.SameCycle a b) :
    (P.vertexBoundary a).length = (P.vertexBoundary b).length := by
  simp only [vertexBoundary_length]
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [← hn]
  exact (Function.minimalPeriod_apply_iterate (P.rotation.injective.mem_periodicPts a) n).symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

variable {D : Type*} [Finite D] {P : RibbonMap D} (B : Bigon P)

/-- The vertex equivalence sends every surviving incidence to its original vertex. -/
theorem verticesEquiv_vertexOf (d : B.Dart) :
    B.verticesEquiv (B.suppress.vertexOf d) = P.vertexOf d.val := rfl

/-- Inclusion preserves and reflects the actual vertex relation. -/
theorem sameVertex_iff (d e : B.Dart) :
    B.suppress.rotation.SameCycle d e ↔ P.rotation.SameCycle d.val e.val := by
  constructor
  · intro h
    have hh := congrArg B.verticesEquiv (Quotient.sound h)
    exact Quotient.exact hh
  · intro h
    have hh : B.suppress.vertexOf d = B.suppress.vertexOf e :=
      B.verticesEquiv.injective (Quotient.sound h)
    exact Quotient.exact hh

omit [Finite D] in
/-- Collapsing a deleted incidence changes its basepoint only within its original vertex. -/
theorem collapse_original_vertex (d : D) : P.rotation.SameCycle (B.collapse d).val d := by
  classical
  by_cases hl : d = P.edge B.left
  · rw [hl, B.collapse_mate_left]
    change P.rotation.SameCycle B.right (P.edge B.left)
    rw [← B.rotation_right]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  · by_cases hr : d = P.edge B.right
    · rw [hr, B.collapse_mate_right]
      change P.rotation.SameCycle B.left (P.edge B.right)
      rw [← B.rotation_left]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    · change P.rotation.SameCycle (B.collapse (⟨d, hl, hr⟩ : B.Dart).val).val d
      rw [B.collapse_survivor]

/-- The marked vertex and every other original vertex retain their exact identity. -/
theorem collapse_sameVertex_iff (a : D) (d : B.Dart) :
    B.suppress.rotation.SameCycle (B.collapse a) d ↔ P.rotation.SameCycle a d.val := by
  rw [B.sameVertex_iff]
  constructor
  · intro h
    exact (B.collapse_original_vertex a).symm.trans h
  · intro h
    exact (B.collapse_original_vertex a).trans h

/-- The terminal coordinate of a compressed block lies on its starting vertex. -/
theorem faceCoordinate_original_vertex (d : B.Dart) :
    P.rotation.SameCycle d.val (B.faceCoordinate d) := by
  have hh := (B.sameVertex_iff d (B.suppress.rotation d)).mp
    (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  change P.rotation.SameCycle d.val (B.rotation d).val at hh
  rw [B.rotation_exchange] at hh
  exact Equiv.Perm.sameCycle_apply_right.mp hh

/-- Bigon suppression cannot increase the number of incidences at a surviving vertex. -/
theorem vertexBoundary_length_le (d : B.Dart) :
    (B.suppress.vertexBoundary d).length ≤ (P.vertexBoundary d.val).length := by
  let block : D → List D := fun x ↦ [x]
  have hnon := B.blocks_nonempty block (fun _ ↦ by simp [block])
  have hlen (l : List B.Dart) : l.length ≤ (l.flatMap (B.blocks block)).length := by
    induction l with
    | nil => simp
    | cons e l ih =>
      have hp := List.length_pos_iff.mpr (hnon e)
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      omega
  have hword : ((B.suppress.vertexBoundary d).flatMap (B.blocks block)).length =
      (P.vertexBoundary d.val).length := by
    simpa [block] using congrArg List.length (B.vertex_word block d)
  rw [← hword]
  exact hlen _

/-- A marked degree bound survives compression even when its chosen dart is deleted. -/
theorem collapse_vertexBoundary_length_le (a : D) :
    (B.suppress.vertexBoundary (B.collapse a)).length ≤ (P.vertexBoundary a).length := by
  exact (B.vertexBoundary_length_le _).trans_eq
    (P.vertexBoundary_length_eq_of_sameCycle (B.collapse_original_vertex a))

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
