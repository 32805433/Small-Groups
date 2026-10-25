module

public import SmallPresentation.SmallCancellationDipoleRelativeFactorRotation
public import SmallPresentation.SmallCancellationDipoleRelativeSplice

/-! Factor support and alternating markers survive the actual positive-anchor splice. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling.FactorCorners

open PermutationCycles

variable {D A : Type*} {G : A → Type*} [∀ a, Group (G a)] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)} (C : FactorCorners G L)
include C

/-- Changing negative-marker successors retains every local coefficient-factor condition. -/
theorem withRotation (τ : Equiv.Perm D)
    (hpos : ∀ d, (L.arc d).2 = true → τ d = P.rotation d) :
    FactorCorners G (L.withRotation τ) where
  alternating := L.alternating_of_positive_successors τ C.alternating hpos
  positive_tag d hd := by
    change (L.arc (τ d)).1 = (L.arc d).1
    rw [hpos d hd]
    exact C.positive_tag d hd
  negative_one := C.negative_one
  coefficient := C.coefficient

/-- The predecessor of an actual positive marker edge belongs to that same factor. -/
theorem positive_face_tag (a : D) (ha : (L.arc a).2 = true) :
    (L.arc (P.face a)).1 = (L.arc a).1 := by
  have hp := C.positive_tag (P.face a) ((L.face_phase C.alternating a).trans ha)
  rw [RibbonMap.face_apply, Equiv.apply_symm_apply] at hp
  have he := congrArg Prod.fst (L.edge_arc a)
  exact hp.symm.trans he

/-- The complete factor and phase data survive the anchor merge and its exact coefficient transfer. -/
theorem edgeSplice (a : D) (ha : (L.arc a).2 = true) :
    FactorCorners G (P.edgeSpliceLabelling L a) := by
  classical
  have hpa : (L.arc (P.face a)).2 = true := (L.face_phase C.alternating a).trans ha
  have htag := C.positive_face_tag a ha
  have hstep : P.rotation (P.face a) = P.edge a := by
    rw [RibbonMap.face_apply, Equiv.apply_symm_apply]
  have hphase : (L.arc (P.edge a)).2 = (L.arc (P.rotation a)).2 := by
    have hh := congrArg Prod.snd (L.edge_arc a)
    exact hh.trans (C.alternating a).symm
  have hswap (x : D) : (L.arc (Equiv.swap (P.rotation a) (P.edge a) x)).2 = (L.arc x).2 := by
    by_cases hl : x = P.rotation a
    · rw [hl, Equiv.swap_apply_left]
      exact hphase
    · by_cases hr : x = P.edge a
      · rw [hr, Equiv.swap_apply_right]
        exact hphase.symm
      · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
  constructor
  · intro d
    change (L.arc (cutAt P.rotation (P.rotation a) (P.edge a) d)).2 = _
    rw [cutAt_apply, hswap]
    exact C.alternating d
  · intro d hd
    change (L.arc (cutAt P.rotation (P.rotation a) (P.edge a) d)).1 = (L.arc d).1
    rw [cutAt_apply]
    by_cases hl : P.rotation d = P.rotation a
    · have hda := P.rotation.injective hl
      rw [hda, Equiv.swap_apply_left]
      have he := congrArg Prod.fst (L.edge_arc a)
      exact he
    · by_cases hr : P.rotation d = P.edge a
      · rw [hr, Equiv.swap_apply_right]
        have he := congrArg Prod.fst (L.edge_arc a)
        have ht := C.positive_tag d hd
        rw [hr] at ht
        exact (C.positive_tag a ha).trans (he.symm.trans ht)
      · rw [Equiv.swap_apply_of_ne_of_ne hl hr]
        exact C.positive_tag d hd
  · intro d hd
    change (L.arc d).2 = false at hd
    have hn : d ≠ a := by intro h; subst d; rw [ha] at hd; contradiction
    have hp : d ≠ P.face a := by intro h; subst d; rw [hpa] at hd; contradiction
    change (if d = a then 1 else L.corner d * if d = P.face a then L.corner a else 1) = 1
    rw [ite_eq_right hn, ite_eq_right hp, mul_one]
    exact C.negative_one d hd
  · intro d
    change (if d = a then 1 else L.corner d * if d = P.face a then L.corner a else 1) ∈
      (Monoid.CoprodI.of : G (L.arc d).1 →* Monoid.CoprodI G).range
    by_cases ha' : d = a
    · rw [ite_eq_left ha']
      exact one_mem _
    · rw [ite_eq_right ha']
      apply mul_mem (C.coefficient d)
      by_cases hp : d = P.face a
      · rw [ite_eq_left hp, hp, htag]
        exact C.coefficient a
      · rw [ite_eq_right hp]
        exact one_mem _

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling.FactorCorners
