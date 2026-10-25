module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsSuppression

/-! Degree-two suppression removes exactly the two interior face darts from each face walk. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.DegreeTwoVertex

open PermutationCycles

variable {D : Type*} {P : RibbonMap D} (C : DegreeTwoVertex P)

def fromSurvivor (d : D) (hd : d ≠ C.left ∧ d ≠ C.right) : C.Dart := C.dartEquiv.symm ⟨d, hd⟩

theorem rotation_symm_val (d : C.Dart) :
    (C.suppress.rotation.symm d).val = P.rotation.symm d.val := by
  have h := C.rotation_val (C.suppress.rotation.symm d)
  rw [Equiv.apply_symm_apply] at h
  have hh := congrArg P.rotation.symm h
  simpa only [Equiv.symm_apply_apply] using hh.symm

theorem face_eq_left_iff (d : D) : P.face d = C.left ↔ d = P.edge C.right := by
  constructor
  · intro h
    have hh := congrArg P.rotation h
    simp only [RibbonMap.face_apply, Equiv.apply_symm_apply, C.rotation_left] at hh
    exact (P.edge_involutive d).symm.trans (congrArg P.edge hh)
  · intro h
    apply P.rotation.injective
    simp only [RibbonMap.face_apply, Equiv.apply_symm_apply, C.rotation_left, h,
      P.edge_involutive C.right]

theorem face_eq_right_iff (d : D) : P.face d = C.right ↔ d = P.edge C.left := by
  constructor
  · intro h
    have hh := congrArg P.rotation h
    simp only [RibbonMap.face_apply, Equiv.apply_symm_apply, C.rotation_right] at hh
    exact (P.edge_involutive d).symm.trans (congrArg P.edge hh)
  · intro h
    apply P.rotation.injective
    simp only [RibbonMap.face_apply, Equiv.apply_symm_apply, C.rotation_right, h,
      P.edge_involutive C.left]

theorem face_left_survives : P.face C.left ≠ C.left ∧ P.face C.left ≠ C.right := by
  constructor
  · intro he
    have h := (C.face_eq_left_iff C.left).mp he
    apply C.mate_ne_right
    rw [h, P.edge_involutive C.right]
  · intro he
    exact (P.edge_ne C.left).symm ((C.face_eq_right_iff C.left).mp he)

theorem face_right_survives : P.face C.right ≠ C.left ∧ P.face C.right ≠ C.right := by
  constructor
  · intro he
    exact (P.edge_ne C.right).symm ((C.face_eq_left_iff C.right).mp he)
  · intro he
    exact C.mate_ne_right.symm ((C.face_eq_right_iff C.right).mp he)

open Classical in
/-- The new face successor skips one removed degree-two dart whenever it encounters one. -/
theorem face_val (d : C.Dart) :
    (C.suppress.face d).val =
      if P.face d.val = C.left then P.face C.left
      else if P.face d.val = C.right then P.face C.right else P.face d.val := by
  classical
  change (C.suppress.rotation.symm (C.suppress.edge d)).val = _
  rw [C.rotation_symm_val, C.edge_val]
  by_cases hl : P.face d.val = C.left
  · have hd := (C.face_eq_left_iff _).mp hl
    have hn : d.val ≠ P.edge C.left := by
      rw [hd]
      exact P.edge.injective.ne C.ne.symm
    rw [ite_eq_left hl, ite_eq_right hn, ite_eq_left hd]
    rfl
  · rw [ite_eq_right hl]
    by_cases hr : P.face d.val = C.right
    · have hd := (C.face_eq_right_iff _).mp hr
      rw [ite_eq_left hr, ite_eq_left hd]
      rfl
    · have hd₁ : d.val ≠ P.edge C.left := fun h ↦ hr ((C.face_eq_right_iff _).mpr h)
      have hd₂ : d.val ≠ P.edge C.right := fun h ↦ hl ((C.face_eq_left_iff _).mpr h)
      rw [ite_eq_right hr, ite_eq_right hd₁, ite_eq_right hd₂]
      rfl

open Classical in
/-- Deleting degree-two incidences filters the precise original face departure walk. -/
theorem delete_face_walk {d e : D} {l : List D} (h : Walk P.face d e l)
    (hd : d ≠ C.left ∧ d ≠ C.right) (he : e ≠ C.left ∧ e ≠ C.right) :
    ∃ l' : List C.Dart,
      Walk C.suppress.face (C.fromSurvivor d hd) (C.fromSurvivor e he) l' ∧
      l'.map Subtype.val = l.filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
  classical
  cases h with
  | nil d => exact ⟨[], .nil _, rfl⟩
  | cons d e rest ht =>
    by_cases hl : P.face d = C.left
    · cases ht with
      | nil => exact False.elim (he.1 hl)
      | cons _ _ rest ht =>
        have ht' : Walk P.face (P.face C.left) e rest := by simpa only [hl] using ht
        obtain ⟨out, hw, hm⟩ := delete_face_walk ht' C.face_left_survives he
        let first := C.fromSurvivor d hd
        have hs : C.suppress.face first = C.fromSurvivor (P.face C.left) C.face_left_survives := by
          apply Subtype.ext
          simp only [C.face_val, fromSurvivor, dartEquiv, Equiv.coe_fn_symm_mk, first, hl,
            ite_true]
        refine ⟨first :: out, ?_, ?_⟩
        · apply Walk.cons
          rw [hs]
          exact hw
        · change d :: out.map Subtype.val = _
          rw [hm]
          simp [hd, hl]
    · by_cases hr : P.face d = C.right
      · cases ht with
        | nil => exact False.elim (he.2 hr)
        | cons _ _ rest ht =>
          have ht' : Walk P.face (P.face C.right) e rest := by simpa only [hr] using ht
          obtain ⟨out, hw, hm⟩ := delete_face_walk ht' C.face_right_survives he
          let first := C.fromSurvivor d hd
          have hs : C.suppress.face first = C.fromSurvivor (P.face C.right) C.face_right_survives := by
            apply Subtype.ext
            simp only [C.face_val, fromSurvivor, dartEquiv, Equiv.coe_fn_symm_mk, first, hr, C.ne.symm,
              ite_true, ite_false]
          refine ⟨first :: out, ?_, ?_⟩
          · apply Walk.cons
            rw [hs]
            exact hw
          · change d :: out.map Subtype.val = _
            rw [hm]
            simp [hd, hr]
      · have hn : P.face d ≠ C.left ∧ P.face d ≠ C.right := ⟨hl, hr⟩
        obtain ⟨out, hw, hm⟩ := delete_face_walk ht hn he
        let first := C.fromSurvivor d hd
        have hs : C.suppress.face first = C.fromSurvivor (P.face d) hn := by
          apply Subtype.ext
          simp only [C.face_val, fromSurvivor, dartEquiv, Equiv.coe_fn_symm_mk, first, hl, hr,
            ite_false]
        refine ⟨first :: out, ?_, ?_⟩
        · apply Walk.cons
          rw [hs]
          exact hw
        · change d :: out.map Subtype.val = _
          rw [hm]
          simp [hd]
termination_by l.length

open Classical in
/-- Exact face boundary after deleting the two degree-two incidences. -/
theorem faceBoundary_filter [Finite D] (d : C.Dart) :
    (C.suppress.faceBoundary d).map Subtype.val =
      (P.faceBoundary d.val).filter (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
  classical
  obtain ⟨l, hw, hm⟩ := C.delete_face_walk (cycleBoundary_walk P.face d.val)
    (C.dartEquiv d).property (C.dartEquiv d).property
  have hnd : l.Nodup := by
    apply List.Nodup.of_map
    rw [hm]
    exact (cycleBoundary_nodup P.face d.val).filter _
  have hn : l ≠ [] := by
    intro hl
    have hs : d.val ∈ (cycleBoundary P.face d.val).filter
        (fun x ↦ decide (x ≠ C.left ∧ x ≠ C.right)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨mem_cycleBoundary_self _ _, (C.dartEquiv d).property⟩
    rw [← hm, hl] at hs
    exact List.not_mem_nil hs
  have hl := hw.eq_cycleBoundary hn hnd
  rw [hl] at hm
  exact hm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.DegreeTwoVertex
