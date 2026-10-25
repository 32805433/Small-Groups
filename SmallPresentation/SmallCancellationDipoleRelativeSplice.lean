module

public import SmallPresentation.SmallCancellationDipoleSplice
public import SmallPresentation.SmallCancellationGeometryRelativeCornerFaces

/-!
# Relative labels and face equations at an actual dipole anchor splice

Splicing the two endpoint vertices across an actual marker edge splits off its one-corner
face. Transfer that corner coefficient to the next old face corner and label the new monogon
by one. The new region equations follow from the original equations, including the affected
face: the split-off factor is explicitly proved trivial.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*} [Finite D] (σ : Equiv.Perm D)

/-- Every point of a split cycle lies on one of the two actual new cycles. -/
theorem cutAt_cycle_cover (a b d : D) (hne : a ≠ b) (hab : σ.SameCycle a b)
    (had : σ.SameCycle a d) :
    (cutAt σ a b).SameCycle a d ∨ (cutAt σ a b).SameCycle b d := by
  have hn := cutAt_not_sameCycle_of_sameCycle σ a b hne hab
  have hh := cycleBoundary_cutAt_merge (cutAt σ a b) a b hn
  rw [cutAt_cutAt] at hh
  have hm : d ∈ cycleBoundary σ a := by
    let k := (orbitEquiv σ a).symm ⟨d, had⟩
    refine List.mem_ofFn.mpr ⟨k, ?_⟩
    exact congrArg Subtype.val ((orbitEquiv σ a).apply_symm_apply ⟨d, had⟩)
  rw [hh, List.mem_append] at hm
  rcases hm with hm | hm
  · left
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hm
    rw [← hk]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  · right
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hm
    rw [← hk]
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)

end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D X H : Type*} [Finite D] [Group H] (P : RibbonMap D)
    (L : RibbonLabelling P X H) (a : D)

omit [Finite D] in
/-- The anchor splice cuts the old face immediately after the anchor itself. -/
theorem edgeSplice_face : (P.edgeSplice a).face = cutAt P.face (P.face a) a := by
  rw [edgeSplice, P.vertexCut_face, Equiv.symm_apply_apply]
  change cutAt P.face a (P.face a) = _
  classical
  simp only [cutAt, Equiv.swap_comm a (P.face a)]

omit [Finite D] in
theorem edgeSplice_face_fixed : (P.edgeSplice a).face a = a := by
  classical
  rw [P.edgeSplice_face, cutAt_apply, Equiv.swap_apply_left]

open Classical in
/-- Move the old anchor corner coefficient into its next face corner and create a trivial monogon. -/
noncomputable def edgeSpliceLabelling : RibbonLabelling (P.edgeSplice a) X H where
  arc := L.arc
  corner d := if d = a then 1 else L.corner d * if d = P.face a then L.corner a else 1
  edge_arc := L.edge_arc

omit [Finite D] in
theorem edgeSplice_inverse_corner (hne : P.face a ≠ a) (d : D) :
    ((P.edgeSpliceLabelling L a).corner d)⁻¹ =
      transferWeight (fun e ↦ (L.corner e)⁻¹) (P.face a) a d := by
  classical
  by_cases ha : d = a <;> by_cases hp : d = P.face a <;>
    simp_all [edgeSpliceLabelling, transferWeight, mul_inv_rev]

omit [Finite D] in
theorem edgeSplice_faceValue (hne : P.face a ≠ a) (d : D) :
    (P.edgeSpliceLabelling L a).faceValue d =
      cycleProduct (cutAt P.face (P.face a) a)
        (transferWeight (fun e ↦ (L.corner e)⁻¹) (P.face a) a) d := by
  simp only [RibbonLabelling.faceValue, RibbonMap.faceBoundary, P.edgeSplice_face,
    cycleProduct, cycleBoundary, Equiv.Perm.coe_pow]
  congr 1
  apply List.map_congr_left
  intro e _
  exact P.edgeSplice_inverse_corner L a hne e

omit [Finite D] in
/-- The new face is a literal one-corner face whose coefficient is one. -/
theorem edgeSplice_anchor_face : (P.edgeSpliceLabelling L a).faceValue a = 1 := by
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (P.edgeSplice_face_fixed a)
  simp [RibbonLabelling.faceValue, RibbonMap.faceBoundary, hp, edgeSpliceLabelling]

theorem edgeSplice_remaining_face (hne : P.face a ≠ a) (hface : L.faceValue (P.face a) = 1) :
    (P.edgeSpliceLabelling L a).faceValue (P.face a) = 1 := by
  rw [P.edgeSplice_faceValue L a hne]
  apply (cut_transfer_split_eq_one_iff P.face (fun e ↦ (L.corner e)⁻¹)
    (P.face a) a hne (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)) ?_).mpr
  · rw [← P.edgeSplice_faceValue L a hne]
    exact P.edgeSplice_anchor_face L a
  · exact hface

theorem edgeSplice_unaffected_face (hne : P.face a ≠ a) (d : D)
    (hp : ¬P.face.SameCycle d (P.face a)) (ha : ¬P.face.SameCycle d a) :
    (P.edgeSpliceLabelling L a).faceValue d = L.faceValue d := by
  rw [P.edgeSplice_faceValue L a hne, cycleProduct_cutAt_unchanged P.face _ _ _ d hp ha]
  apply cycleProduct_eq_of_agree
  intro e he
  have hep : e ≠ P.face a := fun h ↦ hp (h ▸ he)
  have hea : e ≠ a := fun h ↦ ha (h ▸ he)
  simp only [transferWeight, ite_eq_right hep, ite_eq_right hea]

/-- All actual region equations survive the anchor splice and its explicitly trivial new face. -/
theorem edgeSplice_all_faces (hne : P.face a ≠ a) (hfaces : ∀ d, L.faceValue d = 1) :
    ∀ d, (P.edgeSpliceLabelling L a).faceValue d = 1 := by
  intro d
  by_cases hd : P.face.SameCycle (P.face a) d
  · have hc := cutAt_cycle_cover P.face (P.face a) a d hne
      (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)) hd
    rw [← P.edgeSplice_face] at hc
    rcases hc with hc | hc
    · exact ((P.edgeSpliceLabelling L a).faceValue_eq_one_of_sameCycle hc).mp
        (P.edgeSplice_remaining_face L a hne (hfaces _))
    · exact ((P.edgeSpliceLabelling L a).faceValue_eq_one_of_sameCycle hc).mp
        (P.edgeSplice_anchor_face L a)
  · rw [P.edgeSplice_unaffected_face L a hne d (fun h ↦ hd h.symm) ?_]
    · exact hfaces d
    · intro h
      exact hd ((Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _)).trans h.symm)

omit [Finite D] in
/-- At an aligned inverse-row edge, the transferred predecessor coefficient is also one. -/
theorem edgeSplice_predecessor_corner
    (hcoeff : L.corner (P.face a) = (L.corner a)⁻¹) :
    (P.edgeSpliceLabelling L a).corner (P.face a) = 1 := by
  classical
  by_cases h : P.face a = a
  · simp only [edgeSpliceLabelling, h, ↓reduceIte]
  · simp only [edgeSpliceLabelling, ite_eq_right h, ↓reduceIte, hcoeff, inv_mul_cancel]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
