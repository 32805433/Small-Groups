module

public import SmallPresentation.SmallCancellationGeometryRelativeCornerUnchanged
public import SmallPresentation.SmallCancellationGeometryRelativeCornerFaces

/-!
# Finite normalization of a marked factor vertex

The marked coefficient product is arbitrary. Actual adjacent cancellations reduce its
alternating marker cycle to two incidences, retaining every other vertex word and every
surviving based coefficient product. Region equations are deliberately separate: a cut
can split a component and its formerly single outside region.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace FactorVertexShape

variable {D X H : Type*} [Group H] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {a : D} (F : FactorVertexShape L a)

include F in
/-- Marking a different incidence of the same factor vertex changes no shape condition. -/
theorem rebase (b : D) (hb : P.rotation.SameCycle a b) : FactorVertexShape L b where
  tag d hd := (F.tag d (hb.trans hd)).trans (F.tag b hb).symm
  alternating d hd := F.alternating d (hb.trans hd)
  negative d hd := F.negative d (hb.trans hd)

end FactorVertexShape

universe u v w z

/-- Exact surviving data after normalizing one marked vertex to a pair. -/
structure MarkedFactorReduction {D : Type u} {E : Type u} {X : Type v} {H : Type w}
    [Finite D] [Finite E] [Group H] (P : RibbonMap D) (L : RibbonLabelling P X H) (a : D) where
  map : RibbonMap E
  labels : RibbonLabelling map X H
  inclusion : E ↪ D
  marked : E
  shape : FactorVertexShape labels marked
  negative : (labels.arc marked).2 = false
  terminal : map.rotation (map.rotation marked) = marked
  original_marked : P.rotation.SameCycle a (inclusion marked)
  sameVertex : ∀ d e, map.rotation.SameCycle d e ↔
    P.rotation.SameCycle (inclusion d) (inclusion e)
  arc_eq : ∀ e, labels.arc e = L.arc (inclusion e)
  product_eq : ∀ e, ((map.vertexBoundary e).map labels.corner).prod =
    ((P.vertexBoundary (inclusion e)).map L.corner).prod
  other_word : ∀ e, ¬P.rotation.SameCycle a (inclusion e) →
    labels.vertexWord e = L.vertexWord (inclusion e)
  other_reverse_word : ∀ e, ¬P.rotation.SameCycle a (inclusion e) →
    labels.reverseVertexWord e = L.reverseVertexWord (inclusion e)
  other_survives : ∀ d, ¬P.rotation.SameCycle a d → ∃ e, inclusion e = d
  euler : P.EulerEquality → map.EulerEquality
  potential : ∀ (Q : Type z) [Group Q] (q : H →* Q) (F : CornerPotential L q),
    ∃ F' : CornerPotential labels q, ∀ e, F'.value e = F.value (inclusion e)

namespace FactorVertexShape

/-- Repeated genuine corner cancellations leave exactly two markers at a selected factor
vertex, without imposing that its coefficient product be trivial. -/
theorem exists_normalized (D : Type u) [Fintype D] {X : Type v} {H : Type w} [Group H]
    (P : RibbonMap D) (L : RibbonLabelling P X H) (a : D) (F : FactorVertexShape L a) :
    ∃ (E : Type u) (_ : Fintype E), Nonempty (MarkedFactorReduction (E := E) P L a) := by
  classical
  obtain ⟨d, hd, hs⟩ := F.exists_negative
  by_cases ht : P.rotation (P.rotation d) = d
  · refine ⟨D, inferInstance, ⟨{
      map := P
      labels := L
      inclusion := Function.Embedding.refl D
      marked := d
      shape := F.rebase d hd
      negative := hs
      terminal := ht
      original_marked := hd
      sameVertex := fun _ _ ↦ Iff.rfl
      arc_eq := fun _ ↦ rfl
      product_eq := fun _ ↦ rfl
      other_word := fun _ _ ↦ rfl
      other_reverse_word := fun _ _ ↦ rfl
      other_survives := fun e _ ↦ ⟨e, rfl⟩
      euler := fun h ↦ h
      potential := fun _ _ _ paths ↦ ⟨paths, fun _ ↦ rfl⟩ }⟩⟩
  · let C := F.cancellation d hd hs
    let M := C.labelling L (F.cancellation_arc d hd hs)
    let b : C.Dart := ⟨P.rotation (P.rotation d), ht, by
      intro h
      have hh := P.rotation.injective h
      exact C.ne hh.symm⟩
    have hb : P.rotation.SameCycle a b.val :=
      Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.sameCycle_apply_right.mpr hd)
    let Fb : FactorVertexShape M b := F.cancel d hd hs b hb
    obtain ⟨E, inst, ⟨T⟩⟩ := exists_normalized C.Dart C.delete M b Fb
    let : Fintype E := inst
    let inc : E ↪ D := T.inclusion.trans ⟨Subtype.val, Subtype.val_injective⟩
    have hmark : P.rotation.SameCycle a (inc T.marked) :=
      hb.trans ((C.sameVertex_iff _ _).mp T.original_marked)
    have outside (e : E) (he : ¬P.rotation.SameCycle a (inc e)) :
        ¬C.delete.rotation.SameCycle b (T.inclusion e) := by
      intro h
      exact he (hb.trans ((C.sameVertex_iff _ _).mp h))
    have outside_original (e : E) (he : ¬P.rotation.SameCycle a (inc e)) :
        ¬P.rotation.SameCycle C.left (T.inclusion e).val := by
      intro h
      exact he (hd.trans h)
    refine ⟨E, inst, ⟨{
      map := T.map
      labels := T.labels
      inclusion := inc
      marked := T.marked
      shape := T.shape
      negative := T.negative
      terminal := T.terminal
      original_marked := hmark
      sameVertex := fun e f ↦ (T.sameVertex e f).trans (C.sameVertex_iff _ _)
      arc_eq := fun e ↦ T.arc_eq e
      product_eq := fun e ↦ (T.product_eq e).trans (F.cancel_vertex_product d hd hs _)
      other_word := fun e he ↦ (T.other_word e (outside e he)).trans
        (C.vertexWord_unchanged L (F.cancellation_arc d hd hs) _ (outside_original e he))
      other_reverse_word := fun e he ↦ (T.other_reverse_word e (outside e he)).trans
        (C.reverseVertexWord_unchanged L (F.cancellation_arc d hd hs) _
          (outside_original e he))
      other_survives := ?_
      euler := fun h ↦ T.euler (C.delete_euler h)
      potential := fun Q _ q paths ↦ T.potential Q q
        (paths.cancel C (F.cancellation_arc d hd hs) (F.cancellation_corner d hd hs)) }⟩⟩
    intro x hx
    let x' : C.Dart := ⟨x, by
      constructor
      · intro h
        exact hx (h ▸ hd)
      · intro h
        have hr : P.rotation.SameCycle a C.right := Equiv.Perm.sameCycle_apply_right.mpr hd
        exact hx (h ▸ hr)⟩
    have hx' : ¬C.delete.rotation.SameCycle b x' := by
      intro h
      exact hx (hb.trans ((C.sameVertex_iff _ _).mp h))
    obtain ⟨e, he⟩ := T.other_survives x' hx'
    exact ⟨e, congrArg Subtype.val he⟩
termination_by Fintype.card D
decreasing_by exact C.card_darts_lt

end FactorVertexShape
namespace MarkedFactorReduction

variable {D E : Type u} {X : Type v} {H : Type w}
    [Finite D] [Finite E] [Group H] {P : RibbonMap D} {L : RibbonLabelling P X H} {a : D}
    (T : MarkedFactorReduction (E := E) P L a)

/-- The normalized marked cycle has exactly the two displayed incidences. -/
theorem marked_boundary :
    T.map.vertexBoundary T.marked = [T.marked, T.map.rotation T.marked] :=
  (T.shape.cancellation T.marked (.refl _ _) T.negative).vertexBoundary_of_two_cycle T.terminal

/-- A nontrivial marked coefficient remains nontrivial in the single surviving positive
corner; cyclic rebasing introduces no assumption that the original product is one. -/
theorem positive_corner_ne_one
    (hprod : ((P.vertexBoundary a).map L.corner).prod ≠ 1) :
    T.labels.corner (T.map.rotation T.marked) ≠ 1 := by
  intro h
  have ht := T.shape.terminal_product T.marked (.refl _ _) T.negative T.terminal
  have hp := (T.product_eq T.marked).symm.trans (ht.trans h)
  exact hprod ((PermutationCycles.cycleProduct_eq_one_of_sameCycle P.rotation L.corner
    T.original_marked).mpr hp)

end MarkedFactorReduction

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
