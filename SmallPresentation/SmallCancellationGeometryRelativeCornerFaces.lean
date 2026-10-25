module

public import SmallPresentation.SmallCancellationGeometryRelativeCornerLabels
public import SmallPresentation.SmallCancellationGeometryRelativeCornerProducts
public import SmallPresentation.SmallCancellationGeometryCornerCancellationFaces

/-!
# Actual affected region products at an adjacent-corner cut

Before deleting the split-off two-corner vertex, transfer its following coefficient to the
preceding surviving corner. The face permutation is exactly a cut at those two coefficient
positions. The resulting formulas distinguish merging from splitting and never infer two
trivial region products from their product alone.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}

/-- A relative region equation is independent of the chosen boundary incidence. -/
theorem faceValue_eq_one_of_sameCycle (L : RibbonLabelling P X H) {a b : D}
    (h : P.face.SameCycle a b) : L.faceValue a = 1 ↔ L.faceValue b = 1 := by
  simpa only [PermutationCycles.cycleProduct, PermutationCycles.cycleBoundary, faceValue,
    RibbonMap.faceBoundary, Equiv.Perm.coe_pow] using
    PermutationCycles.cycleProduct_eq_one_of_sameCycle P.face (fun e ↦ (L.corner e)⁻¹) h

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation

open PermutationCycles

variable {D X H : Type*} [Group H] {P : RibbonMap D}
variable (C : AdjacentCancellation P) (L : RibbonLabelling P X H)

/-- The corner immediately before the cancelled pair. It survives unless the entire vertex
consists of that pair. -/
def predecessor : D := P.rotation.symm C.left

theorem predecessor_ne_right (hn : P.rotation C.right ≠ C.left) : C.predecessor ≠ C.right := by
  intro he
  apply hn
  rw [← he]
  exact P.rotation.apply_symm_apply C.left

theorem predecessor_ne_left : C.predecessor ≠ C.left := by
  intro he
  have hh := congrArg P.rotation he
  apply C.ne
  simpa only [predecessor, Equiv.apply_symm_apply, C.next] using hh

/-- Exact cut coordinates on the original face permutation. -/
theorem split_face : C.split.face = cutAt P.face C.predecessor C.right := by
  simpa only [split, predecessor, Equiv.symm_apply_apply] using
    P.vertexCut_face C.left (P.rotation C.right)

open Classical in
/-- Transfer coefficients before the split-off two-corner vertex is suppressed. -/
noncomputable def splitLabelling : RibbonLabelling C.split X H where
  arc := L.arc
  corner d := if d = C.right then 1 else
    L.corner d * if P.rotation d = C.left then L.corner C.right else 1
  edge_arc := L.edge_arc

/-- Surviving corner labels agree with the actual cancellation labeling. -/
theorem splitLabelling_corner_survivor
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (d : C.Dart) :
    (C.splitLabelling L).corner d.val = (C.labelling L harc).corner d := by
  simp [splitLabelling, labelling, d.property.2]

@[simp] theorem splitLabelling_corner_right : (C.splitLabelling L).corner C.right = 1 := by
  simp [splitLabelling]

theorem splitLabelling_corner_left (h : L.corner C.left = 1) :
    (C.splitLabelling L).corner C.left = 1 := by
  simp [splitLabelling, C.ne, C.next, C.ne.symm, h]

/-- The inverse corner weights are exactly the transferred face weights. -/
theorem splitLabelling_inverse_corner (hn : P.rotation C.right ≠ C.left) (d : D) :
    ((C.splitLabelling L).corner d)⁻¹ =
      transferWeight (fun e ↦ (L.corner e)⁻¹) C.predecessor C.right d := by
  classical
  have hiff : P.rotation d = C.left ↔ d = C.predecessor :=
    P.rotation.eq_symm_apply.symm
  have hpb := C.predecessor_ne_right hn
  change (if d = C.right then 1 else
    L.corner d * if P.rotation d = C.left then L.corner C.right else 1)⁻¹ = _
  simp only [hiff, transferWeight]
  by_cases hp : d = C.predecessor <;> by_cases hb : d = C.right <;>
    simp_all [mul_inv_rev]

/-- The split's region product is the exact cut-and-transfer product on the old face cycle. -/
theorem splitLabelling_faceValue [Finite D] (hn : P.rotation C.right ≠ C.left) (d : D) :
    (C.splitLabelling L).faceValue d = cycleProduct (cutAt P.face C.predecessor C.right)
      (transferWeight (fun e ↦ (L.corner e)⁻¹) C.predecessor C.right) d := by
  simp only [RibbonLabelling.faceValue, RibbonMap.faceBoundary, C.split_face,
    cycleProduct, cycleBoundary, Equiv.Perm.coe_pow]
  congr 1
  apply List.map_congr_left
  intro e _
  exact C.splitLabelling_inverse_corner L hn e

/-- If the two affected regions were distinct and both valid, their merged region is valid. -/
theorem splitLabelling_merged_face [Finite D] (hn : P.rotation C.right ≠ C.left)
    (hf : ¬ P.face.SameCycle C.predecessor C.right)
    (hp : L.faceValue C.predecessor = 1) (hb : L.faceValue C.right = 1) :
    (C.splitLabelling L).faceValue C.predecessor = 1 := by
  rw [C.splitLabelling_faceValue L hn]
  apply cut_transfer_merge_eq_one P.face (fun e ↦ (L.corner e)⁻¹) _ _ hf
  · simpa only [cycleProduct, cycleBoundary, RibbonLabelling.faceValue,
      RibbonMap.faceBoundary, Equiv.Perm.coe_pow] using hp
  · simpa only [cycleProduct, cycleBoundary, RibbonLabelling.faceValue,
      RibbonMap.faceBoundary, Equiv.Perm.coe_pow] using hb

/-- For a split of one valid region, proving the old-only side's product suffices to recover
the equation on the retained side. This is the exact interface to the radial boundary theorem. -/
theorem splitLabelling_split_face_iff [Finite D] (hn : P.rotation C.right ≠ C.left)
    (hf : P.face.SameCycle C.predecessor C.right) (hp : L.faceValue C.predecessor = 1) :
    (C.splitLabelling L).faceValue C.predecessor = 1 ↔
      (C.splitLabelling L).faceValue C.right = 1 := by
  rw [C.splitLabelling_faceValue L hn, C.splitLabelling_faceValue L hn]
  apply cut_transfer_split_eq_one_iff P.face (fun e ↦ (L.corner e)⁻¹) _ _
    (C.predecessor_ne_right hn) hf
  simpa only [cycleProduct, cycleBoundary, RibbonLabelling.faceValue,
    RibbonMap.faceBoundary, Equiv.Perm.coe_pow] using hp

/-- Every region disjoint from the affected two face cycles retains its entire product. -/
theorem splitLabelling_unaffected_face [Finite D] (hn : P.rotation C.right ≠ C.left) (d : D)
    (hp : ¬ P.face.SameCycle d C.predecessor) (hb : ¬ P.face.SameCycle d C.right) :
    (C.splitLabelling L).faceValue d = L.faceValue d := by
  rw [C.splitLabelling_faceValue L hn,
    cycleProduct_cutAt_unchanged P.face _ C.predecessor C.right d hp hb]
  change cycleProduct P.face _ d = cycleProduct P.face _ d
  apply cycleProduct_eq_of_agree
  intro e he
  have hpe : e ≠ C.predecessor := fun hh ↦ hp (hh ▸ he)
  have hbe : e ≠ C.right := fun hh ↦ hb (hh ▸ he)
  simp [transferWeight, hpe, hbe]

/-- The complete vertex boundary when the cancelled pair is the entire vertex. -/
theorem vertexBoundary_of_two_cycle (htwo : P.rotation C.right = C.left) :
    P.vertexBoundary C.left = [C.left, C.right] := by
  have hw : Walk P.rotation C.left C.left [C.left, C.right] := by
    apply Walk.cons
    rw [C.next]
    apply Walk.cons
    rw [htwo]
    exact .nil _
  have hh := hw.eq_cycleBoundary (by simp) (by simp [C.ne])
  simpa only [cycleBoundary, RibbonMap.vertexBoundary, Equiv.Perm.coe_pow] using hh.symm

/-- The entire old two-corner vertex can disappear only after its final coefficient is
shown trivial by the actual old vertex equation. -/
theorem corner_right_eq_one_of_two_cycle
    (htwo : P.rotation C.right = C.left) (hleft : L.corner C.left = 1)
    (hvertex : ((P.vertexBoundary C.left).map L.corner).prod = 1) : L.corner C.right = 1 := by
  simpa [C.vertexBoundary_of_two_cycle htwo, hleft] using hvertex

/-- No surviving predecessor exists for an entire deleted two-corner vertex, so every
surviving coefficient is literally unchanged. -/
theorem labelling_corner_of_two_cycle
    (harc : L.arc C.right = reverseLetter (L.arc C.left))
    (htwo : P.rotation C.right = C.left) (d : C.Dart) :
    (C.labelling L harc).corner d = L.corner d.val := by
  apply C.labelling_corner_of_ne L harc d
  intro hh
  exact d.property.2 (P.rotation.injective (hh.trans htwo.symm))

/-- Removing the split-off two-corner vertex preserves every surviving face product,
since both removed coefficients have become one. This includes isolated loops and complete
two-corner vertices and does not make any unjustified claim about the preceding face split. -/
theorem delete_faceValue [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (d : C.Dart) : (C.labelling L harc).faceValue d = (C.splitLabelling L).faceValue d.val := by
  classical
  calc
    (C.labelling L harc).faceValue d =
        (((C.delete.faceBoundary d).map Subtype.val).map
          (fun e ↦ ((C.splitLabelling L).corner e)⁻¹)).prod := by
      simp only [RibbonLabelling.faceValue, List.map_map, Function.comp_def]
      apply congrArg List.prod
      apply List.map_congr_left
      intro e _
      rw [C.splitLabelling_corner_survivor L harc e]
    _ = (((C.split.faceBoundary d.val).filter
          (fun e ↦ decide (e ≠ C.left ∧ e ≠ C.right))).map
          (fun e ↦ ((C.splitLabelling L).corner e)⁻¹)).prod := by
      rw [C.faceBoundary_filter]
    _ = (C.splitLabelling L).faceValue d.val := by
      apply prod_filter_of_trivial_deleted
      intro e _ he
      have hh : e = C.left ∨ e = C.right := by simpa only [decide_eq_false_iff_not,
        not_and_or, not_not] using he
      rcases hh with rfl | rfl
      · simp [C.splitLabelling_corner_left L hleft]
      · simp

/-- For an entire two-corner vertex with both coefficients one, the intermediate split
labeling and the original labeling give identical face products. -/
theorem splitLabelling_faceValue_of_two_cycle [Finite D]
    (htwo : P.rotation C.right = C.left) (hright : L.corner C.right = 1) (d : D) :
    (C.splitLabelling L).faceValue d = L.faceValue d := by
  have hcorner (e : D) : (C.splitLabelling L).corner e = L.corner e := by
    by_cases he : e = C.right
    · simp [splitLabelling, he, hright]
    · have hn : P.rotation e ≠ C.left := fun h ↦ he (P.rotation.injective (h.trans htwo.symm))
      simp [splitLabelling, he, hn]
  simp only [RibbonLabelling.faceValue, hcorner, C.split_eq_of_two_cycle htwo]

/-- Complete two-corner old-vertex deletion preserves each surviving face equation directly. -/
theorem delete_faceValue_of_two_cycle [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left))
    (htwo : P.rotation C.right = C.left) (hleft : L.corner C.left = 1)
    (hvertex : ((P.vertexBoundary C.left).map L.corner).prod = 1) (d : C.Dart) :
    (C.labelling L harc).faceValue d = L.faceValue d.val := by
  rw [C.delete_faceValue L harc hleft d]
  exact C.splitLabelling_faceValue_of_two_cycle L htwo
    (C.corner_right_eq_one_of_two_cycle L htwo hleft hvertex) d.val

/-- The final merged face satisfies its equation whenever both former faces did. -/
theorem delete_merged_face [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (hn : P.rotation C.right ≠ C.left) (hf : ¬ P.face.SameCycle C.predecessor C.right)
    (hp : L.faceValue C.predecessor = 1) (hb : L.faceValue C.right = 1)
    (d : C.Dart) (hd : C.split.face.SameCycle C.predecessor d.val) :
    (C.labelling L harc).faceValue d = 1 := by
  rw [C.delete_faceValue L harc hleft]
  exact ((C.splitLabelling L).faceValue_eq_one_of_sameCycle hd).mp
    (C.splitLabelling_merged_face L hn hf hp hb)

/-- The final equation on one side of an affected face split follows from the equation on
the other surviving side, when the old face was valid. -/
theorem delete_split_face_iff [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (hn : P.rotation C.right ≠ C.left) (hf : P.face.SameCycle C.predecessor C.right)
    (hp : L.faceValue C.predecessor = 1)
    (d e : C.Dart) (hd : C.split.face.SameCycle C.predecessor d.val)
    (he : C.split.face.SameCycle C.right e.val) :
    (C.labelling L harc).faceValue d = 1 ↔ (C.labelling L harc).faceValue e = 1 := by
  rw [C.delete_faceValue L harc hleft, C.delete_faceValue L harc hleft]
  exact ((C.splitLabelling L).faceValue_eq_one_of_sameCycle hd).symm.trans
    ((C.splitLabelling_split_face_iff L hn hf hp).trans
      ((C.splitLabelling L).faceValue_eq_one_of_sameCycle he))

/-- Every unaffected original face retains its equation after the complete actual surgery. -/
theorem delete_unaffected_face [Finite D]
    (harc : L.arc C.right = reverseLetter (L.arc C.left)) (hleft : L.corner C.left = 1)
    (hn : P.rotation C.right ≠ C.left) (d : C.Dart)
    (hp : ¬ P.face.SameCycle d.val C.predecessor) (hb : ¬ P.face.SameCycle d.val C.right) :
    (C.labelling L harc).faceValue d = L.faceValue d.val := by
  rw [C.delete_faceValue L harc hleft]
  exact C.splitLabelling_unaffected_face L hn d.val hp hb

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AdjacentCancellation
