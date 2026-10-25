module

public import SmallPresentation.SmallCancellationGeometryCorridorMergeCycles
public import SmallPresentation.SmallCancellationDipolePairRefinement

/-! Doubling cycle refinements and retaining a marked negative anchor splice. -/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*}

/-- Double each original incidence into its positive and negative marker phases. -/
def doublePerm (σ : Equiv.Perm D) : Equiv.Perm (D × Bool) where
  toFun
    | (d, false) => (d, true)
    | (d, true) => (σ d, false)
  invFun
    | (d, false) => (σ.symm d, true)
    | (d, true) => (d, false)
  left_inv := by rintro ⟨d, b⟩; cases b <;> simp
  right_inv := by rintro ⟨d, b⟩; cases b <;> simp

@[simp] theorem doublePerm_false (σ : Equiv.Perm D) (d : D) :
    doublePerm σ (d, false) = (d, true) := rfl

@[simp] theorem doublePerm_true (σ : Equiv.Perm D) (d : D) :
    doublePerm σ (d, true) = (σ d, false) := rfl

/-- Actual vertex cuts whose targets are positive markers only. -/
inductive PositiveSplitRefinement : Equiv.Perm (D × Bool) → Equiv.Perm (D × Bool) → Prop
  | refl (σ) : PositiveSplitRefinement σ σ
  | cut {σ τ} : PositiveSplitRefinement σ τ → (a b : D) → a ≠ b →
      τ.SameCycle (a, false) (b, false) →
      PositiveSplitRefinement σ (cutAt τ (a, false) (b, false))

namespace PositiveSplitRefinement

theorem toSplitRefinement {σ τ : Equiv.Perm (D × Bool)} (h : PositiveSplitRefinement σ τ) :
    SplitRefinement σ τ := by
  induction h with
  | refl => exact .refl _
  | cut h a b hn hc ih => exact .cut ih _ _ (fun h ↦ hn (congrArg Prod.fst h)) hc

theorem trans {σ τ κ : Equiv.Perm (D × Bool)}
    (h₁ : PositiveSplitRefinement σ τ) (h₂ : PositiveSplitRefinement τ κ) :
    PositiveSplitRefinement σ κ := by
  induction h₂ with
  | refl => exact h₁
  | cut h a b hn hc ih => exact .cut ih a b hn hc

/-- Cuts at positive targets preserve every successor whose phase was negative. -/
theorem agree_on_negative_successors {σ τ : Equiv.Perm (D × Bool)}
    (h : PositiveSplitRefinement σ τ) (d : D × Bool) (hd : (σ d).2 = true) :
    τ d = σ d := by
  classical
  induction h with
  | refl => rfl
  | cut h a b hn hc ih =>
    rw [cutAt_apply, ih]
    have ha : σ d ≠ (a, false) := by intro he; have := congrArg Prod.snd he; simp_all
    have hb : σ d ≠ (b, false) := by intro he; have := congrArg Prod.snd he; simp_all
    simp [Equiv.swap_apply_def, ha, hb]

end PositiveSplitRefinement

theorem doublePerm_projects (σ : Equiv.Perm D) (d : D × Bool) :
    σ.SameCycle d.1 (doublePerm σ d).1 := by
  rcases d with ⟨d, b⟩
  cases b
  · exact .refl _ _
  · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

theorem doublePerm_lifts (σ : Equiv.Perm D) (d : D) :
    (doublePerm σ).SameCycle (d, false) (σ d, false) := by
  have ha : (doublePerm σ).SameCycle (d, false) (d, true) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  have hb : (doublePerm σ).SameCycle (d, true) (σ d, false) :=
    Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
  exact ha.trans hb

/-- Doubling retains exactly the original cycle relation, independently of marker phase. -/
theorem doublePerm_sameCycle_iff [Finite D] (σ : Equiv.Perm D) (a b : D) (p q : Bool) :
    (doublePerm σ).SameCycle (a, p) (b, q) ↔ σ.SameCycle a b := by
  constructor
  · exact sameCycle_map_of_step (doublePerm σ) σ Prod.fst (doublePerm_projects σ)
  · intro h
    have hh := sameCycle_map_of_step σ (doublePerm σ) (fun d ↦ (d, false))
      (doublePerm_lifts σ) h
    have ha : (doublePerm σ).SameCycle (a, false) (a, p) := by
      cases p
      · exact .refl _ _
      · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    have hb : (doublePerm σ).SameCycle (b, false) (b, q) := by
      cases q
      · exact .refl _ _
      · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)
    exact ha.symm.trans (hh.trans hb)

/-- A base cut doubles to a cut at the positive marker targets. -/
theorem doublePerm_cut (σ : Equiv.Perm D) (a b : D) :
    doublePerm (cutAt σ a b) = cutAt (doublePerm σ) (a, false) (b, false) := by
  classical
  apply Equiv.ext
  intro d
  rcases d with ⟨d, p⟩
  cases p
  · simp only [doublePerm_false, cutAt_apply, Equiv.swap_apply_def]
    simp
  · simp only [doublePerm_true, cutAt_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all

/-- Positive and negative incoming-target switches commute. -/
theorem cutAt_opposite_phases (σ : Equiv.Perm (D × Bool)) (a b c d : D) :
    cutAt (cutAt σ (a, false) (b, false)) (c, true) (d, true) =
      cutAt (cutAt σ (c, true) (d, true)) (a, false) (b, false) := by
  classical
  apply Equiv.ext
  intro x
  simp only [cutAt_apply]
  obtain ⟨y, p, hp⟩ := Prod.exists.mp (show ∃ y : D × Bool, y = σ x from ⟨σ x, rfl⟩)
  rw [← hp]
  cases p
  · by_cases ha : y = a <;> by_cases hb : y = b <;> simp [Equiv.swap_apply_def, ha, hb]
  · by_cases hc : y = c <;> by_cases hd : y = d <;> simp [Equiv.swap_apply_def, hc, hd]

/-- Cutting inside one cycle can only refine the original cycle relation. -/
theorem sameCycle_cutAt_refines [Finite D] (σ : Equiv.Perm D) (a b : D)
    (hab : σ.SameCycle a b) {d e : D} (h : (cutAt σ a b).SameCycle d e) :
    σ.SameCycle d e := by
  classical
  apply sameCycle_map_of_step (cutAt σ a b) σ id ?_ h
  intro x
  change σ.SameCycle x (Equiv.swap a b (σ x))
  by_cases ha : σ x = a
  · rw [ha, Equiv.swap_apply_left]
    exact (Equiv.Perm.sameCycle_apply_right.mpr (.refl σ x)).trans (ha ▸ hab)
  · by_cases hb : σ x = b
    · rw [hb, Equiv.swap_apply_right]
      exact (Equiv.Perm.sameCycle_apply_right.mpr (.refl σ x)).trans (hb ▸ hab.symm)
    · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
      exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

theorem SplitRefinement.sameCycle_refines [Finite D] {σ τ : Equiv.Perm D}
    (h : SplitRefinement σ τ) {a b : D} (hab : τ.SameCycle a b) : σ.SameCycle a b := by
  induction h with
  | refl => exact hab
  | @cut τ h c d hne hc ih => exact ih (sameCycle_cutAt_refines τ c d hc hab)

/-- Every actual base refinement lifts to positive-target refinement of its doubled markers. -/
theorem SplitRefinement.double [Finite D] {σ τ : Equiv.Perm D} (h : SplitRefinement σ τ) :
    PositiveSplitRefinement (doublePerm σ) (doublePerm τ) := by
  induction h with
  | refl => exact .refl _
  | @cut τ h a b hn hc ih =>
    rw [doublePerm_cut]
    exact .cut ih a b hn ((doublePerm_sameCycle_iff τ a b false false).mpr hc)

/-- A lifted positive cut stays a split after a negative anchor cut, provided the
anchor endpoints still belong to one final base cycle. -/
theorem double_cut_anchor_step [Finite D] (σ : Equiv.Perm D) (u v a b : D)
    (huv : u ≠ v) (hcycle : σ.SameCycle u v) (hab : a ≠ b)
    (hfinal : (cutAt σ u v).SameCycle a b) :
    (cutAt (doublePerm σ) (a, true) (b, true)).SameCycle (u, false) (v, false) := by
  classical
  let S := doublePerm σ
  let U := cutAt S (u, false) (v, false)
  let V := cutAt S (a, true) (b, true)
  let W := cutAt U (a, true) (b, true)
  let W' := cutAt V (u, false) (v, false)
  let := Fintype.ofFinite (Cycles S)
  let := Fintype.ofFinite (Cycles U)
  let := Fintype.ofFinite (Cycles V)
  let := Fintype.ofFinite (Cycles W)
  let := Fintype.ofFinite (Cycles W')
  have hp : S.SameCycle (u, false) (v, false) :=
    (doublePerm_sameCycle_iff σ u v false false).mpr hcycle
  have hn : S.SameCycle (a, true) (b, true) :=
    (doublePerm_sameCycle_iff σ a b true true).mpr
      (sameCycle_cutAt_refines σ u v hcycle hfinal)
  have hn' : U.SameCycle (a, true) (b, true) := by
    have hh := (doublePerm_sameCycle_iff (cutAt σ u v) a b true true).mpr hfinal
    rw [doublePerm_cut] at hh
    exact hh
  have hnp : (u, false) ≠ (v, false) := fun h ↦ huv (congrArg Prod.fst h)
  have hnn : (a, true) ≠ (b, true) := fun h ↦ hab (congrArg Prod.fst h)
  have hc₁ := card_cutAt_of_sameCycle S (u, false) (v, false) hnp hp
  have hc₂ := card_cutAt_of_sameCycle S (a, true) (b, true) hnn hn
  have hc₃ := card_cutAt_of_sameCycle U (a, true) (b, true) hnn hn'
  by_contra hnot
  have hc₄ := card_cutAt_of_not_sameCycle V (u, false) (v, false) hnot
  have hcomm : W = W' := cutAt_opposite_phases S u v a b
  change Fintype.card (Cycles U) = Fintype.card (Cycles S) + 1 at hc₁
  change Fintype.card (Cycles V) = Fintype.card (Cycles S) + 1 at hc₂
  change Fintype.card (Cycles W) = Fintype.card (Cycles U) + 1 at hc₃
  change Fintype.card (Cycles V) = Fintype.card (Cycles W') + 1 at hc₄
  simp only [Fintype.card_eq_nat_card] at hc₁ hc₂ hc₃ hc₄
  rw [hcomm] at hc₃
  omega

/-- A fixed negative anchor cut can be carried through all lifted base refinements,
using only positive-target cuts. -/
theorem SplitRefinement.double_with_anchor [Finite D] {σ τ : Equiv.Perm D}
    (h : SplitRefinement σ τ) (a b : D) (hab : a ≠ b) (hfinal : τ.SameCycle a b) :
    PositiveSplitRefinement (cutAt (doublePerm σ) (a, true) (b, true))
      (cutAt (doublePerm τ) (a, true) (b, true)) := by
  induction h with
  | refl => exact .refl _
  | @cut τ h u v huv hcycle ih =>
    have hold : τ.SameCycle a b := sameCycle_cutAt_refines τ u v hcycle hfinal
    have hh := ih hold
    rw [doublePerm_cut, cutAt_opposite_phases]
    exact .cut hh u v huv (double_cut_anchor_step τ u v a b huv hcycle hab hfinal)

/-- Refining two spliced original cycles into paired base blocks lifts to positive-only
cuts after the actual negative-phase marker anchor splice. -/
theorem double_anchor_refinement [Finite D] (σ τ : Equiv.Perm D) (a b : D)
    (hsep : ¬σ.SameCycle a b) (h : SplitRefinement (cutAt σ (σ a) b) τ)
    (hfinal : τ.SameCycle a b) :
    PositiveSplitRefinement (cutAt (doublePerm σ) (a, true) (b, true))
      (cutAt (doublePerm τ) (a, true) (b, true)) := by
  have hab : a ≠ b := fun h ↦ hsep (h ▸ .refl _ _)
  have hsab : σ a ≠ b := by
    intro h
    exact hsep (h ▸ Equiv.Perm.sameCycle_apply_right.mpr (.refl σ a))
  have hsep' : ¬(doublePerm σ).SameCycle (a, true) (b, true) :=
    mt (doublePerm_sameCycle_iff σ a b true true).mp hsep
  have hjoined : (cutAt (doublePerm σ) (a, true) (b, true)).SameCycle
      (σ a, false) (b, false) := by
    apply (sameCycle_cutAt_merge_iff (doublePerm σ) (a, true) (b, true) hsep' _ _).mpr
    right
    constructor
    · left
      exact (doublePerm_sameCycle_iff σ (σ a) a false true).mpr
        (Equiv.Perm.sameCycle_apply_left.mpr (.refl _ _))
    · right
      exact (doublePerm_sameCycle_iff σ b b false true).mpr (.refl _ _)
  have hfirst : PositiveSplitRefinement (cutAt (doublePerm σ) (a, true) (b, true))
      (cutAt (doublePerm (cutAt σ (σ a) b)) (a, true) (b, true)) := by
    rw [doublePerm_cut, cutAt_opposite_phases]
    exact .cut (.refl _) (σ a) b hsab hjoined
  exact hfirst.trans (h.double_with_anchor a b hab hfinal)

/-- The four-marker factor blocks, with the anchor factor split into its two trivial pairs. -/
noncomputable def pairFactorRotation {n : ℕ} (k : Fin n) :
    Equiv.Perm ((Fin n ⊕ Fin n) × Bool) :=
  cutAt (doublePerm (RelativeSmallCancellation.Geometry.RowDeletion.interchange (reverseFin n)))
    (Sum.inl k, true) (Sum.inr k.rev, true)

/-- The actual anchor splice of two opposite row circles splits into old factor blocks
by cuts whose targets are positive markers only. -/
theorem pairFactorRotation_refinement {n : ℕ} (k : Fin n) :
    PositiveSplitRefinement
      (cutAt (doublePerm (Equiv.sumCongr (finRotate n) (finRotate n)))
        (Sum.inl k, true) (Sum.inr k.rev, true))
      (pairFactorRotation k) := by
  apply double_anchor_refinement
  · intro hc
    have hh := constant_on_cycles
      (Equiv.sumCongr (finRotate n) (finRotate n)) Sum.isLeft
      (by intro d; cases d <;> rfl) hc
    cases hh
  · exact anchored_pairing_refinement k
  · exact Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _)

end SmallPresentationStatements.PermutationCycles
