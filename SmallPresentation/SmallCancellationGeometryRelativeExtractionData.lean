module

public import SmallPresentation.SmallCancellationGeometryRelativeCornerFaces
public import SmallPresentation.SmallCancellationGeometryRelativeCornerUnchanged
public import SmallPresentation.SmallCancellationGeometryRelativeRestriction

/-!
# Local bookkeeping for old-disc extraction

Old/new status is an actual rotation-invariant predicate on incidences. Cancelling an old
vertex preserves that predicate and all factor-disc equations at other old vertices. New
relator readings and quotient potentials can therefore be retained through the same
surviving-incidence inclusion.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

variable {D : Type*} [Finite D] (P : RibbonMap D)

theorem vertex_predicate_constant (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) {d e : D}
    (h : P.rotation.SameCycle d e) : old d ↔ old e :=
  Iff.of_eq (PermutationCycles.constant_on_cycles P.rotation old (fun d ↦ propext (hold d)) h)

end RibbonMap

namespace AdjacentCancellation

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}
variable (C : AdjacentCancellation P) (L : RibbonLabelling P X H)
variable (harc : L.arc C.right = reverseLetter (L.arc C.left))

omit [Finite D] in
theorem retained_old_invariant (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) (d : C.Dart) :
    old (C.delete.rotation d).val ↔ old d.val := by
  classical
  rw [C.rotation_val]
  by_cases hn : P.rotation d.val = C.left
  · rw [ite_eq_left hn]
    have hlr : old C.right ↔ old C.left := by simpa only [C.next] using hold C.left
    have hrd : old C.left ↔ old d.val := by simpa only [hn] using hold d.val
    exact (hold C.right).trans (hlr.trans hrd)
  · rw [ite_eq_right hn]
    exact hold d.val

/-- A factor disc at another vertex is retained by the same actual cancellation; no
coefficient or cyclic-order condition is replaced by an assumed normal-form conclusion. -/
theorem factorDisc_other (d : C.Dart) (hd : ¬ P.rotation.SameCycle C.left d.val)
    (F : FactorDisc L d.val) (hleft : L.corner C.left = 1) :
    FactorDisc (C.labelling L harc) d := by
  have oldcycle (e : C.Dart) (he : C.delete.rotation.SameCycle d e) :
      P.rotation.SameCycle d.val e.val := (C.sameVertex_iff d e).mp he
  have hpred (e : C.Dart) (he : C.delete.rotation.SameCycle d e) :
      P.rotation e.val ≠ C.left := by
    intro hh
    have hs : P.rotation.SameCycle e.val C.left := by
      have hstep : P.rotation.SameCycle e.val (P.rotation e.val) :=
        Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      simpa only [hh] using hstep
    exact hd (hs.symm.trans (oldcycle e he).symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    exact F.tag e.val (oldcycle e he)
  · intro e he
    change (L.arc (C.delete.rotation e).val).2 = !((L.arc e.val).2)
    rw [C.rotation_val, ite_eq_right (hpred e he)]
    exact F.alternating e.val (oldcycle e he)
  · intro e he hs
    rw [C.labelling_corner_of_ne L harc e (hpred e he)]
    exact F.negative e.val (oldcycle e he) hs
  · have hh := C.vertex_value L harc hleft (fun _ ↦ (1 : H))
      (fun _ ↦ (inv_one).symm) (MonoidHom.id H) d
    simp only [MonoidHom.id_apply, one_mul] at hh
    exact hh.trans F.product

end AdjacentCancellation
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
