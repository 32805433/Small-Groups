module

public import SmallPresentation.SmallCancellationGeometryFactorDisc
public import SmallPresentation.SmallCancellationBandPieces

/-! Old-disc cancellation preserves every other actual based relator word literally. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}
    (C : AdjacentCancellation P) (L : RibbonLabelling P X H)
    (harc : L.arc C.right = reverseLetter (L.arc C.left))

theorem other_vertex_avoids (d : C.Dart) (hd : ¬P.rotation.SameCycle C.left d.val)
    (e : D) (he : e ∈ P.vertexBoundary d.val) : e ≠ C.left ∧ e ≠ C.right := by
  have hde := (P.mem_vertexBoundary_iff d.val e).mp he
  constructor
  · intro h
    subst e
    exact hd hde.symm
  · intro h
    subst e
    have hlr : P.rotation.SameCycle C.left C.right := by
      rw [← C.next]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact hd (hlr.trans hde.symm)

/-- The original departure list of every other vertex is retained literally. -/
theorem vertexBoundary_unchanged (d : C.Dart) (hd : ¬P.rotation.SameCycle C.left d.val) :
    (C.delete.vertexBoundary d).map Subtype.val = P.vertexBoundary d.val := by
  classical
  rw [C.vertexBoundary_filter]
  apply List.filter_eq_self.mpr
  intro e he
  simpa only [decide_eq_true_eq] using C.other_vertex_avoids d hd e he

/-- Every arc and coefficient in a different original relator vertex is unchanged. -/
theorem vertexWord_unchanged (d : C.Dart) (hd : ¬P.rotation.SameCycle C.left d.val) :
    (C.labelling L harc).vertexWord d = L.vertexWord d.val := by
  rw [RibbonLabelling.vertexWord, RibbonLabelling.vertexWord,
    ← C.vertexBoundary_unchanged d hd, List.map_map]
  apply List.map_congr_left
  intro e he
  have hde := (C.delete.mem_vertexBoundary_iff d e).mp he
  have hold := (C.sameVertex_iff d e).mp hde
  have hpred : P.rotation e.val ≠ C.left := by
    intro hh
    have h : P.rotation.SameCycle e.val C.left := by
      have hstep : P.rotation.SameCycle e.val (P.rotation e.val) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      simpa only [hh] using hstep
    exact hd (h.symm.trans hold.symm)
  apply Prod.ext
  · rfl
  · exact C.labelling_corner_of_ne L harc e hpred

omit [Finite D] in
theorem inverse_iterate_sameVertex (d : C.Dart) (k : ℕ) :
    C.delete.rotation.SameCycle d (C.delete.rotation.symm^[k] d) := by
  apply Equiv.Perm.SameCycle.of_inv
  exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)

theorem other_vertex_inverse_iterate (d : C.Dart)
    (hd : ¬P.rotation.SameCycle C.left d.val) (k : ℕ) :
    (C.delete.rotation.symm^[k] d).val = P.rotation.symm^[k] d.val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', C.rotation_symm_val]
    have hh := (C.sameVertex_iff d _).mp (C.inverse_iterate_sameVertex d k)
    have hn : (C.delete.rotation.symm^[k] d).val ≠ P.rotation C.right := by
      intro he
      have hc : P.rotation.SameCycle C.left (P.rotation C.right) := by
        have hlr : P.rotation.SameCycle C.left C.right := by
          rw [← C.next]
          exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
        exact Equiv.Perm.sameCycle_apply_right.mpr hlr
      have hcd : P.rotation.SameCycle C.left (C.delete.rotation.symm^[k] d).val := by
        simpa only [he] using hc
      exact hd (hcd.trans hh.symm)
    rw [ite_eq_right hn, ih, Function.iterate_succ_apply']

/-- Reverse readings at unchanged relator vertices retain their exact shifted inverse corners. -/
theorem reverseVertexWord_unchanged (d : C.Dart)
    (hd : ¬P.rotation.SameCycle C.left d.val) :
    (C.labelling L harc).reverseVertexWord d = L.reverseVertexWord d.val := by
  have hp : Function.minimalPeriod C.delete.rotation d =
      Function.minimalPeriod P.rotation d.val := by
    simpa only [List.length_map, RibbonMap.vertexBoundary_length] using
      congrArg List.length (C.vertexBoundary_unchanged d hd)
  simp only [RibbonLabelling.reverseVertexWord, hp]
  apply congrArg List.ofFn
  funext k
  apply Prod.ext
  · change reverseLetter (L.arc (C.delete.rotation.symm^[k.val] d).val) = _
    rw [C.other_vertex_inverse_iterate d hd k.val]
  · have hh := (C.sameVertex_iff d _).mp (C.inverse_iterate_sameVertex d (k.val + 1))
    have hn : P.rotation (C.delete.rotation.symm^[k.val + 1] d).val ≠ C.left := by
      intro he
      have hs : P.rotation.SameCycle (C.delete.rotation.symm^[k.val + 1] d).val C.left := by
        have hs : P.rotation.SameCycle (C.delete.rotation.symm^[k.val + 1] d).val
            (P.rotation (C.delete.rotation.symm^[k.val + 1] d).val) :=
          Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
        simpa only [he] using hs
      exact hd (hs.symm.trans hh.symm)
    change ((C.labelling L harc).corner (C.delete.rotation.symm^[k.val + 1] d))⁻¹ =
      (L.corner (P.rotation.symm^[k.val + 1] d.val))⁻¹
    rw [C.labelling_corner_of_ne L harc _ hn,
      C.other_vertex_inverse_iterate d hd (k.val + 1)]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
