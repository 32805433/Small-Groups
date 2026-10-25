module

public import SmallPresentation.SmallCancellationGeometryFaceCapLabels
public import SmallPresentation.SmallCancellationGeometryMarkedPicture
public import SmallPresentation.SmallCancellationDipoleRelativeFactorRotation

/-! An exceptional unmarked component gives an actual capped marked counterexample. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
open PermutationCycles
variable {D : Type} [Fintype D] {A I : Type} (G : A → Type) [∀ x, Group (G x)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    (P : RibbonMap D) (a : D) (L : RibbonLabelling P A (Monoid.CoprodI G))
    (S : OldDiscSystem L)

/-- The cap adds a marked vertex; it adds no old relation and changes no old one. -/
noncomputable def oldDiscs (h : Monoid.CoprodI G) : OldDiscSystem (label P a L h) where
  old := Sum.elim S.old (fun _ ↦ False)
  invariant := by
    rintro (d | b)
    · exact S.invariant d
    · cases b <;> rfl
  disc := by
    rintro (d | b) hd
    · exact old_factorDisc P a L h d (S.disc d hd)
    · exact False.elim hd

/-- The added marked vertex is disjoint from every original vertex. -/
theorem marked_not_old_cycle (d : D) :
    ¬ (map P a).rotation.SameCycle (.inr false) (.inl d) := by
  intro h
  have hh := ((map P a).mem_vertexBoundary_iff _ _).mpr h
  simp [marked_vertexBoundary] at hh

omit [Fintype D] in
theorem marked_cycle_new (b : Bool) :
    (map P a).rotation.SameCycle (.inr false) (.inr b) := by
  cases b
  · exact .refl _ _
  · rw [← rotation_positive P a]
    exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

/-- Every unmarked attaching incidence of the capped picture is an original attaching
incidence. This function never duplicates or invents an attaching occurrence. -/
def newOriginal (h : Monoid.CoprodI G)
    (d : {d // ¬ (oldDiscs G P a L S h).old d ∧
      ¬ (map P a).rotation.SameCycle (.inr false) d}) : {d // ¬S.old d} := by
  rcases d with ⟨d | b, hd⟩
  · exact ⟨d, hd.1⟩
  · exact False.elim (hd.2 (marked_cycle_new P a b))

theorem newOriginal_inclusion (h : Monoid.CoprodI G)
    (d : {d // ¬ (oldDiscs G P a L S h).old d ∧
      ¬ (map P a).rotation.SameCycle (.inr false) d}) :
    Sum.inl (newOriginal G P a L S h d).val = d.val := by
  rcases d with ⟨d | b, hd⟩
  · rfl
  · exact False.elim (hd.2 (marked_cycle_new P a b))

theorem old_sameCycle_iff (d e : D) :
    (map P a).rotation.SameCycle (.inl d) (.inl e) ↔ P.rotation.SameCycle d e := by
  rw [← (map P a).mem_vertexBoundary_iff, old_vertexBoundary,
    ← P.mem_vertexBoundary_iff]
  simp only [List.mem_map, Sum.inl.injEq, exists_eq_right]

/-- The attaching-incidence inclusion reflects actual vertex cycles exactly. -/
theorem newOriginal_sameCycle (h : Monoid.CoprodI G)
    (d e : {d // ¬ (oldDiscs G P a L S h).old d ∧
      ¬ (map P a).rotation.SameCycle (.inr false) d}) :
    (map P a).rotation.SameCycle d.val e.val ↔
      P.rotation.SameCycle (newOriginal G P a L S h d).val
        (newOriginal G P a L S h e).val := by
  rw [← newOriginal_inclusion G P a L S h d, ← newOriginal_inclusion G P a L S h e,
    old_sameCycle_iff]

/-- The new marked boundary does not change the literal indexed attaching readings. -/
noncomputable def readings (h : Monoid.CoprodI G)
    (R : MixedReadings (rows := rows) S) :
    MarkedMixedReadings G length rows (oldDiscs G P a L S h) (.inr false) where
  origin d := R.origin (newOriginal G P a L S h d)
  forward := by
    rintro (d | b) hd hs
    · rw [old_vertexWord P a L h d]
      exact R.forward d hd.1 hs
    · exact False.elim (hd.2 (marked_cycle_new P a b))
  backward := by
    rintro (d | b) hd hs
    · rw [L.reverseVertexWord_map (label P a L h) Sum.inl Sum.inl_injective
        (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)]
      exact R.backward d hd.1 hs
    · exact False.elim (hd.2 (marked_cycle_new P a b))

/-- A connected unmarked component with a nontrivial exceptional factor face becomes
an actual marked counterexample by adjoining exactly two darts. All original old
relations and indexed attaching readings survive, and every face equation is restored. -/
noncomputable def picture (R : MixedReadings (rows := rows) S)
    (C : RibbonLabelling.FactorCorners G L) (ha : (L.arc a).2 = true)
    (hc : P.Connected) (hE : P.EulerEquality)
    (hregions : ∀ d, ¬P.face.SameCycle (P.face a) d → L.faceValue d = 1)
    (hbad : L.faceValue (P.face a) ≠ 1) :
    MarkedRelativePicture G length rows (D ⊕ Bool) where
  map := FaceCap.map P a
  labels := label P a L (L.faceValue (P.face a))
  marked := .inr false
  marked_size := by rw [marked_vertexBoundary]; rfl
  oldDiscs := oldDiscs G P a L S (L.faceValue (P.face a))
  marked_not_old := id
  shape := marked_shape P a L _ ha
  nontrivial := by rw [marked_product]; exact hbad
  readings := readings G length rows P a L S _ R
  factorCorners := factorCorners P a G L C ha _ (cap_coefficient_mem P a G L C)
  connected := connected P a hc
  euler := euler P a hE
  faces := label_all_faces P a L (opposite_faces P a G L C) hregions

/-- A defective face must be positive; negative faces already consist entirely of
identity coefficients. Thus no extra sign assumption is needed when choosing the cap. -/
theorem positive_of_bad_face (C : RibbonLabelling.FactorCorners G L)
    (hbad : L.faceValue (P.face a) ≠ 1) : (L.arc a).2 = true := by
  cases ha : (L.arc a).2 with
  | true => rfl
  | false =>
    apply False.elim
    apply hbad
    exact L.negative_faceValue C.alternating C.negative_one _
      ((L.face_phase C.alternating a).trans ha)

/-- Cap an exceptional face specified directly by one of its darts. -/
noncomputable def pictureAt (R : MixedReadings (rows := rows) S)
    (C : RibbonLabelling.FactorCorners G L) (hc : P.Connected) (hE : P.EulerEquality)
    (outside : D) (hregions : ∀ d, ¬P.face.SameCycle outside d → L.faceValue d = 1)
    (hbad : L.faceValue outside ≠ 1) :
    MarkedRelativePicture G length rows (D ⊕ Bool) :=
  picture G length rows P (P.face.symm outside) L S R C
    (positive_of_bad_face G P _ L C (by simpa only [Equiv.apply_symm_apply] using hbad))
    hc hE (by simpa only [Equiv.apply_symm_apply] using hregions)
    (by simpa only [Equiv.apply_symm_apply] using hbad)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
