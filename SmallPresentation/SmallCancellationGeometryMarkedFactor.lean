module

public import SmallPresentation.SmallCancellationGeometryCornerPotentialCancellation
public import SmallPresentation.SmallCancellationGeometryBoundaryProducts
public import SmallPresentation.SmallCancellationGeometryCornerCancellationRegions

/-!
# Marked factor vertices with arbitrary coefficient product

Unlike an old relation disc, a marked boundary vertex may have nontrivial total coefficient.
Its alternating factor shape still permits cancellation of adjacent negative-positive markers.
The exact based coefficient product is retained at every surviving incidence.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

open PermutationCycles

variable {D X H : Type*} [Group H] {P : RibbonMap D}

/-- The alternating constant-factor shape, without imposing a relation on the total product. -/
structure FactorVertexShape (L : RibbonLabelling P X H) (a : D) : Prop where
  tag : ∀ d, P.rotation.SameCycle a d → (L.arc d).1 = (L.arc a).1
  alternating : ∀ d, P.rotation.SameCycle a d →
    (L.arc (P.rotation d)).2 = !((L.arc d).2)
  negative : ∀ d, P.rotation.SameCycle a d → (L.arc d).2 = false → L.corner d = 1

namespace FactorVertexShape

variable {L : RibbonLabelling P X H} {a : D} (F : FactorVertexShape L a)

include F in
/-- Every nonempty factor disc contains a negative marker, even if its marked start is positive. -/
theorem exists_negative : ∃ d, P.rotation.SameCycle a d ∧ (L.arc d).2 = false := by
  cases hs : (L.arc a).2 with
  | false => exact ⟨a, .refl _ _, hs⟩
  | true =>
    refine ⟨P.rotation a, Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _), ?_⟩
    simpa [hs] using F.alternating a (.refl _ _)

/-- A negative marker and its successor are a genuine cancellable adjacent pair. -/
def cancellation (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false) :
    AdjacentCancellation P where
  left := d
  right := P.rotation d
  ne := by
    intro he
    have hh := F.alternating d hd
    rw [← he, hs] at hh
    contradiction
  next := rfl

theorem cancellation_arc (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false) :
    L.arc (F.cancellation d hd hs).right = reverseLetter (L.arc (F.cancellation d hd hs).left) := by
  apply Prod.ext
  · exact (F.tag _ (Equiv.Perm.sameCycle_apply_right.mpr hd)).trans (F.tag _ hd).symm
  · exact F.alternating d hd

theorem cancellation_corner (d : D) (hd : P.rotation.SameCycle a d)
    (hs : (L.arc d).2 = false) : L.corner (F.cancellation d hd hs).left = 1 :=
  F.negative d hd hs

variable [Finite D]

/-- Cancelling a chosen negative-positive pair retains the local factor-disc normal form. -/
theorem cancel (d : D) (hd : P.rotation.SameCycle a d) (hs : (L.arc d).2 = false)
    (e : (F.cancellation d hd hs).Dart) (he : P.rotation.SameCycle a e.val) :
    FactorVertexShape ((F.cancellation d hd hs).labelling L (F.cancellation_arc d hd hs)) e := by
  let C := F.cancellation d hd hs
  let M := C.labelling L (F.cancellation_arc d hd hs)
  have left_cycle : P.rotation.SameCycle a C.left := hd
  have left_negative : (L.arc C.left).2 = false := hs
  have right_positive : (L.arc C.right).2 = true := by
    simpa only [C, cancellation, hs, Bool.not_false] using F.alternating d hd
  have oldcycle (x : C.Dart) (hx : C.delete.rotation.SameCycle e x) :
      P.rotation.SameCycle a x.val := he.trans ((C.sameVertex_iff e x).mp hx)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (F.tag _ (oldcycle x hx)).trans (F.tag _ he).symm
  · intro x hx
    change (L.arc (C.delete.rotation x).val).2 = !((L.arc x.val).2)
    rw [C.rotation_val]
    by_cases hl : P.rotation x.val = C.left
    · rw [ite_eq_left hl]
      have hr : P.rotation.SameCycle a C.right :=
        Equiv.Perm.sameCycle_apply_right.mpr left_cycle
      have hsg := F.alternating x.val (oldcycle x hx)
      rw [hl, left_negative] at hsg
      rw [F.alternating C.right hr, right_positive]
      exact hsg
    · rw [ite_eq_right hl]
      exact F.alternating x.val (oldcycle x hx)
  · intro x hx hneg
    change (L.arc x.val).2 = false at hneg
    have hl : P.rotation x.val ≠ C.left := by
      intro hh
      have hsg := F.alternating x.val (oldcycle x hx)
      rw [hh, left_negative, hneg] at hsg
      contradiction
    rw [C.labelling_corner_of_ne L _ x hl]
    exact F.negative x.val (oldcycle x hx) hneg
/-- Every based vertex coefficient product survives this normalization step exactly. -/
theorem cancel_vertex_product (d : D) (hd : P.rotation.SameCycle a d)
    (hs : (L.arc d).2 = false) (e : (F.cancellation d hd hs).Dart) :
    (((F.cancellation d hd hs).delete.vertexBoundary e).map
      ((F.cancellation d hd hs).labelling L (F.cancellation_arc d hd hs)).corner).prod =
      ((P.vertexBoundary e.val).map L.corner).prod := by
  have hh := (F.cancellation d hd hs).vertex_value L (F.cancellation_arc d hd hs)
    (F.cancellation_corner d hd hs) (fun _ ↦ (1 : H)) (fun _ ↦ (inv_one).symm)
    (MonoidHom.id H) e
  simpa only [MonoidHom.id_apply, one_mul] using hh

/-- The nontriviality of a marked boundary coefficient is invariant under rebasing. -/
theorem product_ne_one_at (hprod : ((P.vertexBoundary a).map L.corner).prod ≠ 1)
    (d : D) (hd : P.rotation.SameCycle a d) :
    ((P.vertexBoundary d).map L.corner).prod ≠ 1 := by
  intro h
  exact hprod ((cycleProduct_eq_one_of_sameCycle P.rotation L.corner hd).mpr h)

include F in
omit [Finite D] in
/-- At the terminal two-marker boundary, the positive corner is the whole marked product. -/
theorem terminal_product (d : D) (hd : P.rotation.SameCycle a d)
    (hs : (L.arc d).2 = false) (ht : P.rotation (P.rotation d) = d) :
    ((P.vertexBoundary d).map L.corner).prod = L.corner (P.rotation d) := by
  have hh := (F.cancellation d hd hs).pair_vertex_product L.corner ht
  simpa only [cancellation, F.negative d hd hs, one_mul] using hh

end FactorVertexShape
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
