module

public import SmallPresentation.SmallCancellationGeometryFaceCap

/-! Exact region products after capping one exceptional coefficient face. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap

open PermutationCycles
variable {D X H : Type*} [Finite D] [Group H] (P : RibbonMap D) (a : D)

noncomputable def baseFace : Equiv.Perm (D ⊕ Bool) :=
  Equiv.sumCongr P.face (Equiv.refl Bool)

noncomputable def firstFace : Equiv.Perm (D ⊕ Bool) :=
  cutAt (baseFace P) (.inr false) (.inl (P.face a))

omit [Finite D] in
theorem face_permutation : (map P a).face =
    cutAt (firstFace P a) (.inr true) (.inl (P.face (P.edge a))) := by
  classical
  apply Equiv.ext
  rintro (d | b)
  · by_cases ha : d = a
    · subst d
      rw [face_anchor]
      simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_def, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Bool.false_eq_true, ↓reduceIte]
    · by_cases he : d = P.edge a
      · subst d
        rw [face_mate]
        have hne : P.face (P.edge a) ≠ P.face a := P.face.injective.ne (P.edge_ne a)
        simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_def, Sum.inl.injEq, Sum.inl_ne_inr, hne, ↓reduceIte]
      · rw [face_old P a d ha he]
        have h₁ : P.face d ≠ P.face a := P.face.injective.ne ha
        have h₂ : P.face d ≠ P.face (P.edge a) := P.face.injective.ne he
        simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.swap_apply_def, Sum.inl.injEq, Sum.inl_ne_inr, h₁, h₂, ↓reduceIte]
  · cases b
    · rw [face_positive]
      have hne : P.face a ≠ P.face (P.edge a) := P.face.injective.ne (P.edge_ne a).symm
      simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Equiv.swap_apply_def, Sum.inl.injEq, Sum.inl_ne_inr, hne, ↓reduceIte]
    · rw [face_negative]
      simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Equiv.swap_apply_def, Sum.inr.injEq, Sum.inr_ne_inl, Bool.true_eq_false, ↓reduceIte]

theorem baseFace_boundary_old (d : D) :
    cycleBoundary (baseFace P) (.inl d) = (P.faceBoundary d).map Sum.inl :=
  (cycleBoundary_map_injective P.face (baseFace P) Sum.inl Sum.inl_injective
    (fun _ ↦ rfl) d).symm

omit [Finite D] in
theorem baseFace_boundary_new (b : Bool) :
    cycleBoundary (baseFace P) (.inr b) = [.inr b] := by
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr
    (show baseFace P (.inr b) = .inr b from rfl)
  simp [cycleBoundary, hp]

omit [Finite D] in
theorem baseFace_new_ne_old (b : Bool) (d : D) :
    ¬(baseFace P).SameCycle (.inr b) (.inl d) := by
  intro h
  have hh := h.eq_of_left (show baseFace P (.inr b) = .inr b from rfl)
  cases hh

theorem firstFace_boundary_positive :
    cycleBoundary (firstFace P a) (.inr false) =
      .inr false :: (P.faceBoundary (P.face a)).map Sum.inl := by
  rw [firstFace, cycleBoundary_cutAt_merge _ _ _ (baseFace_new_ne_old P false _),
    baseFace_boundary_new, baseFace_boundary_old]
  rfl

omit [Finite D] in
theorem firstFace_negative_fixed : firstFace P a (.inr true) = .inr true := by
  classical
  simp only [firstFace, baseFace, cutAt_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, Equiv.swap_apply_def, Sum.inr.injEq, Sum.inr_ne_inl, Bool.true_eq_false, ↓reduceIte]

omit [Finite D] in
theorem firstFace_positive_ne_negative :
    ¬(firstFace P a).SameCycle (.inr false) (.inr true) := by
  intro h
  have hh := h.eq_of_right (firstFace_negative_fixed P a)
  cases hh

theorem firstFace_positive_ne_mate
    (hfaces : ¬P.face.SameCycle a (P.edge a)) :
    ¬(firstFace P a).SameCycle (.inr false) (.inl (P.face (P.edge a))) := by
  intro h
  have hm : (Sum.inl (P.face (P.edge a)) : D ⊕ Bool) ∈
      cycleBoundary (firstFace P a) (.inr false) := by
    let k := (orbitEquiv (firstFace P a) (.inr false)).symm ⟨.inl (P.face (P.edge a)), h⟩
    exact List.mem_ofFn.mpr ⟨k, congrArg Subtype.val
      ((orbitEquiv (firstFace P a) (.inr false)).apply_symm_apply _)⟩
  rw [firstFace_boundary_positive, List.mem_cons] at hm
  rcases hm with hm | hm
  · cases hm
  · obtain ⟨d, hd, hde⟩ := List.mem_map.mp hm
    have he : d = P.face (P.edge a) := Sum.inl.inj hde
    subst d
    have hh := (P.mem_faceBoundary_iff _ _).mp hd
    exact hfaces (Equiv.Perm.sameCycle_apply_left.mp (Equiv.Perm.sameCycle_apply_right.mp hh))

/-- The new positive face is the old exceptional boundary preceded by its cap corner. -/
theorem faceBoundary_positive (hfaces : ¬P.face.SameCycle a (P.edge a)) :
    (map P a).faceBoundary (.inr false) =
      .inr false :: (P.faceBoundary (P.face a)).map Sum.inl := by
  change cycleBoundary (map P a).face (.inr false) = _
  rw [face_permutation, cycleBoundary_cutAt_unchanged _ _ _ _
    (firstFace_positive_ne_negative P a) (firstFace_positive_ne_mate P a hfaces)]
  exact firstFace_boundary_positive P a


theorem cycle_mem_iff {E : Type*} [Finite E] (σ : Equiv.Perm E) (d e : E) :
    e ∈ cycleBoundary σ d ↔ σ.SameCycle d e := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp h
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  · intro h
    let k := (orbitEquiv σ d).symm ⟨e, h⟩
    exact List.mem_ofFn.mpr ⟨k, congrArg Subtype.val ((orbitEquiv σ d).apply_symm_apply _)⟩

theorem baseFace_old_cycle_iff (d e : D) :
    (baseFace P).SameCycle (.inl d) (.inl e) ↔ P.face.SameCycle d e := by
  rw [← cycle_mem_iff, baseFace_boundary_old, List.mem_map]
  constructor
  · rintro ⟨x, hx, hxe⟩
    have he := Sum.inl.inj hxe
    subst x
    exact (P.mem_faceBoundary_iff _ _).mp hx
  · intro h
    exact ⟨e, (P.mem_faceBoundary_iff _ _).mpr h, rfl⟩

theorem firstFace_boundary_unaffected (d : D) (hd : ¬P.face.SameCycle d (P.face a)) :
    cycleBoundary (firstFace P a) (.inl d) = (P.faceBoundary d).map Sum.inl := by
  rw [firstFace, cycleBoundary_cutAt_unchanged]
  · exact baseFace_boundary_old P d
  · exact fun h ↦ baseFace_new_ne_old P false d h.symm
  · exact fun h ↦ hd ((baseFace_old_cycle_iff P d _).mp h)

omit [Finite D] in
theorem firstFace_boundary_negative :
    cycleBoundary (firstFace P a) (.inr true) = [.inr true] := by
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr (firstFace_negative_fixed P a)
  simp [cycleBoundary, hp]

/-- The second original face gains only a coefficient-one negative corner. -/
theorem faceBoundary_negative (hfaces : ¬P.face.SameCycle a (P.edge a)) :
    (map P a).faceBoundary (.inr true) =
      .inr true :: (P.faceBoundary (P.face (P.edge a))).map Sum.inl := by
  have hne : ¬(firstFace P a).SameCycle (.inr true) (.inl (P.face (P.edge a))) := by
    intro h
    have hh := h.eq_of_left (firstFace_negative_fixed P a)
    cases hh
  have hc : ¬P.face.SameCycle (P.face (P.edge a)) (P.face a) := by
    intro h
    have hh := Equiv.Perm.sameCycle_apply_left.mp (Equiv.Perm.sameCycle_apply_right.mp h)
    exact hfaces hh.symm
  change cycleBoundary (map P a).face (.inr true) = _
  rw [face_permutation, cycleBoundary_cutAt_merge _ _ _ hne,
    firstFace_boundary_negative, firstFace_boundary_unaffected P a _ hc]
  rfl

/-- Every unaffected old face has its identical original departure list. -/
theorem faceBoundary_unaffected (d : D)
    (ha : ¬P.face.SameCycle d a) (he : ¬P.face.SameCycle d (P.edge a)) :
    (map P a).faceBoundary (.inl d) = (P.faceBoundary d).map Sum.inl := by
  have hc : ¬P.face.SameCycle d (P.face a) := fun h ↦ ha (Equiv.Perm.sameCycle_apply_right.mp h)
  have hv : ¬(firstFace P a).SameCycle (.inl d) (.inr true) := by
    intro h
    have hh := h.eq_of_right (firstFace_negative_fixed P a)
    cases hh
  have hq : ¬(firstFace P a).SameCycle (.inl d) (.inl (P.face (P.edge a))) := by
    intro h
    have hh := (cycle_mem_iff (firstFace P a) _ _).mpr h
    rw [firstFace_boundary_unaffected P a d hc] at hh
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hh
    have hxe' := Sum.inl.inj hxe
    subst x
    exact he (Equiv.Perm.sameCycle_apply_right.mp ((P.mem_faceBoundary_iff _ _).mp hx))
  change cycleBoundary (map P a).face (.inl d) = _
  rw [face_permutation, cycleBoundary_cutAt_unchanged _ _ _ _ hv hq]
  exact firstFace_boundary_unaffected P a d hc

omit [Finite D] in
/-- Old face steps lift through the inserted corner, so their original cycle is retained. -/
theorem face_old_step (d : D) :
    (map P a).face.SameCycle (.inl d) (.inl (P.face d)) := by
  by_cases ha : d = a
  · subst d
    have h₁ : (map P a).face.SameCycle (.inl a) (.inr false) := by
      rw [← face_anchor P a]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    have h₂ : (map P a).face.SameCycle (.inr false) (.inl (P.face a)) := by
      rw [← face_positive P a]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact h₁.trans h₂
  · by_cases he : d = P.edge a
    · subst d
      have h₁ : (map P a).face.SameCycle (.inl (P.edge a)) (.inr true) := by
        rw [← face_mate P a]
        exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      have h₂ : (map P a).face.SameCycle (.inr true) (.inl (P.face (P.edge a))) := by
        rw [← face_negative P a]
        exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      exact h₁.trans h₂
    · rw [← face_old P a d ha he]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

theorem face_cycle_old {d e : D} (h : P.face.SameCycle d e) :
    (map P a).face.SameCycle (.inl d) (.inl e) :=
  sameCycle_map_of_step P.face (map P a).face Sum.inl (face_old_step P a) h


noncomputable def label (L : RibbonLabelling P X H) (h : H) : RibbonLabelling (map P a) X H where
  arc := Sum.elim L.arc (fun b ↦ if b then reverseLetter (L.arc a) else L.arc a)
  corner := Sum.elim L.corner (fun b ↦ if b then 1 else h)
  edge_arc := by
    rintro (d | b)
    · by_cases ha : d = a
      · subst d
        rw [edge_anchor]
        rfl
      · by_cases he : d = P.edge a
        · subst d
          rw [edge_mate]
          change L.arc a = reverseLetter (L.arc (P.edge a))
          rw [L.edge_arc, reverseLetter_reverseLetter]
        · rw [edge_old P a d ha he]
          exact L.edge_arc d
    · cases b
      · rw [edge_positive]
        exact L.edge_arc a
      · rw [edge_negative]
        exact (reverseLetter_reverseLetter (L.arc a)).symm

theorem label_positive_product (L : RibbonLabelling P X H) (h : H)
    (hfaces : ¬P.face.SameCycle a (P.edge a)) :
    (label P a L h).faceValue (.inr false) = h⁻¹ * L.faceValue (P.face a) := by
  simp only [RibbonLabelling.faceValue, faceBoundary_positive P a hfaces,
    List.map_cons, List.map_map, List.prod_cons, label]
  rfl

theorem label_negative_product (L : RibbonLabelling P X H) (h : H)
    (hfaces : ¬P.face.SameCycle a (P.edge a)) :
    (label P a L h).faceValue (.inr true) = L.faceValue (P.face (P.edge a)) := by
  simp only [RibbonLabelling.faceValue, faceBoundary_negative P a hfaces,
    List.map_cons, List.map_map, List.prod_cons, label]
  simp only [Sum.elim_inr, reduceIte, inv_one, one_mul]
  rfl

theorem label_unaffected_product (L : RibbonLabelling P X H) (h : H) (d : D)
    (ha : ¬P.face.SameCycle d a) (he : ¬P.face.SameCycle d (P.edge a)) :
    (label P a L h).faceValue (.inl d) = L.faceValue d := by
  rw [RibbonLabelling.faceValue, faceBoundary_unaffected P a d ha he, List.map_map]
  rfl

/-- Capping one defective face restores all region equations on the actual finite ribbon. -/
theorem label_all_faces (L : RibbonLabelling P X H)
    (hfaces : ¬P.face.SameCycle a (P.edge a))
    (hregions : ∀ d, ¬P.face.SameCycle (P.face a) d → L.faceValue d = 1) :
    ∀ d, (label P a L (L.faceValue (P.face a))).faceValue d = 1 := by
  let M := label P a L (L.faceValue (P.face a))
  have hp : M.faceValue (.inr false) = 1 := by
    rw [label_positive_product P a L _ hfaces, inv_mul_cancel]
  have hn : M.faceValue (.inr true) = 1 := by
    rw [label_negative_product P a L _ hfaces]
    apply hregions
    intro h
    exact hfaces (Equiv.Perm.sameCycle_apply_left.mp (Equiv.Perm.sameCycle_apply_right.mp h))
  rintro (d | b)
  · by_cases ha : P.face.SameCycle (P.face a) d
    · have hstart : (map P a).face.SameCycle (.inr false) (.inl (P.face a)) := by
        rw [← face_positive P a]
        exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
      exact (M.faceValue_eq_one_of_sameCycle (hstart.trans (face_cycle_old P a ha))).mp hp
    · by_cases he : P.face.SameCycle (P.face (P.edge a)) d
      · have hstart : (map P a).face.SameCycle (.inr true) (.inl (P.face (P.edge a))) := by
          rw [← face_negative P a]
          exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
        exact (M.faceValue_eq_one_of_sameCycle (hstart.trans (face_cycle_old P a he))).mp hn
      · rw [label_unaffected_product P a L _ d
          (fun h ↦ ha (Equiv.Perm.sameCycle_apply_left.mpr h.symm))
          (fun h ↦ he (Equiv.Perm.sameCycle_apply_left.mpr h.symm))]
        exact hregions d ha
  · cases b
    · exact hp
    · exact hn

omit [Finite D] in
theorem marked_vertexBoundary : (map P a).vertexBoundary (.inr false) = [.inr false, .inr true] := by
  have hw : Walk (map P a).rotation (.inr false) (.inr false) [.inr false, .inr true] := by
    apply Walk.cons
    rw [rotation_positive]
    apply Walk.cons
    rw [rotation_negative]
    exact .nil _
  exact (hw.eq_cycleBoundary (by simp) (by simp)).symm

omit [Finite D] in
/-- The new two-marker vertex has precisely the capped face product as its marked coefficient. -/
theorem marked_product (L : RibbonLabelling P X H) (h : H) :
    (((map P a).vertexBoundary (.inr false)).map (label P a L h).corner).prod = h := by
  simp [marked_vertexBoundary, label]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
