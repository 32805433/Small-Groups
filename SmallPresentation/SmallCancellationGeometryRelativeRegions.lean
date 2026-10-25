module

public import SmallPresentation.SmallCancellationGeometryCorridorRefinement
public import SmallPresentation.SmallCancellationGeometryEulerComponent
public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler

/-!
# Coefficient-region ribbons obtained by splitting designated vertices

Retain the rotations of old coefficient vertices and split every new relator vertex into
singleton incidences. Original edge pairings are unchanged. Connected components are then
coefficient regions, with new relator incidences as boundary leaves. This construction does
not assert that every region boundary has coefficient product one: multiple boundary cycles
and the nesting of retained relator vertices must still be accounted for.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D : Type*}

open Classical in
/-- Keep specified complete permutation cycles and split all other cycles into singletons. -/
noncomputable def isolateComplement (σ : Equiv.Perm D) (keep : D → Prop)
    (hkeep : ∀ d, keep (σ d) ↔ keep d) : Equiv.Perm D where
  toFun d := if keep d then σ d else d
  invFun d := if keep d then σ.symm d else d
  left_inv d := by
    by_cases hd : keep d
    · simp [hd, (hkeep d).mpr hd]
    · simp [hd]
  right_inv d := by
    have hh : keep (σ.symm d) ↔ keep d := by simpa using (hkeep (σ.symm d)).symm
    by_cases hd : keep d
    · simp [hd, hh.mpr hd]
    · simp [hd]

open Classical in
@[simp] theorem isolateComplement_apply (σ : Equiv.Perm D) (keep : D → Prop)
    (hkeep : ∀ d, keep (σ d) ↔ keep d) (d : D) :
    isolateComplement σ keep hkeep d = if keep d then σ d else d := rfl

/-- Splitting off an unwanted incidence preserves the predicate selecting whole cycles. -/
theorem isolate_cut_invariant (σ : Equiv.Perm D) (keep : D → Prop)
    (hkeep : ∀ d, keep (σ d) ↔ keep d) (a : D) (ha : ¬ keep a) :
    ∀ d, keep (cutAt σ a (σ a) d) ↔ keep d := by
  classical
  intro d
  have hsa : ¬ keep (σ a) := fun h ↦ ha ((hkeep a).mp h)
  rw [cutAt_apply]
  by_cases hd : σ d = a
  · rw [hd, Equiv.swap_apply_left]
    have hkd : ¬ keep d := fun h ↦ ha (hd ▸ (hkeep d).mpr h)
    simp [hsa, hkd]
  · by_cases hda : σ d = σ a
    · rw [hda, Equiv.swap_apply_right]
      have hkd : ¬ keep d := by simpa only [σ.injective hda] using ha
      simp [ha, hkd]
    · rw [Equiv.swap_apply_of_ne_of_ne hd hda]
      exact hkeep d

/-- The eventual isolated rotation is unaffected by splitting off one unwanted incidence. -/
theorem isolate_after_cut (σ : Equiv.Perm D) (keep : D → Prop)
    (hkeep : ∀ d, keep (σ d) ↔ keep d) (a : D) (ha : ¬ keep a) :
    isolateComplement (cutAt σ a (σ a)) keep (isolate_cut_invariant σ keep hkeep a ha) =
      isolateComplement σ keep hkeep := by
  classical
  ext d
  rw [isolateComplement_apply, isolateComplement_apply]
  by_cases hd : keep d
  · rw [ite_eq_left hd, ite_eq_left hd, cutAt_apply]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro hh
      exact ha (hh ▸ (hkeep d).mpr hd)
    · intro hh
      exact ha (σ.injective hh ▸ hd)
  · rw [ite_eq_right hd, ite_eq_right hd]

/-- Every permutation fixed point remains fixed after splitting off a different nonfixed
point; this makes the number of unwanted nonfixed incidences strictly decrease. -/
theorem isolate_cut_fixed (σ : Equiv.Perm D) (a : D) (ha : σ a ≠ a)
    (d : D) (hd : σ d = d) : cutAt σ a (σ a) d = d := by
  classical
  rw [cutAt_apply, hd]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he
    subst d
    exact ha hd
  · intro he
    have hh : σ d = σ a := hd.trans he
    have hh' := σ.injective hh
    exact ha (he.symm.trans hh')

open Classical in
/-- Splitting all unwanted cycles is a finite sequence of genuine vertex cuts. -/
theorem isolateComplement_refinement [Fintype D] (σ : Equiv.Perm D) (keep : D → Prop)
    (hkeep : ∀ d, keep (σ d) ↔ keep d) :
    SplitRefinement σ (isolateComplement σ keep hkeep) := by
  classical
  by_cases hex : ∃ a, ¬ keep a ∧ σ a ≠ a
  · obtain ⟨a, ha, hna⟩ := hex
    have hs := SplitRefinement.single σ a (σ a) hna.symm
      (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
    have ht := isolateComplement_refinement (cutAt σ a (σ a)) keep
      (isolate_cut_invariant σ keep hkeep a ha)
    rw [isolate_after_cut σ keep hkeep a ha] at ht
    exact hs.trans ht
  · have he : isolateComplement σ keep hkeep = σ := by
      ext d
      rw [isolateComplement_apply]
      by_cases hd : keep d
      · exact ite_eq_left hd
      · rw [ite_eq_right hd]
        exact (not_not.mp (fun h ↦ hex ⟨d, hd, h⟩)).symm
    rw [he]
    exact .refl _
termination_by (Finset.univ.filter (fun d ↦ ¬ keep d ∧ σ d ≠ d)).card
decreasing_by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact ⟨hd.1, fun he ↦ hd.2 (isolate_cut_fixed σ a hna d he)⟩
  · intro he
    have hm : a ∈ Finset.univ.filter (fun d ↦ ¬ keep d ∧ σ d ≠ d) := by simp [ha, hna]
    rw [← he] at hm
    exact (Finset.mem_filter.mp hm).2.2 (by simp [cutAt_apply])

end SmallPresentationStatements.PermutationCycles

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap

open PermutationCycles

variable {D X : Type*} (P : RibbonMap D)

/-- The actual coefficient-region ribbon: old vertices retain their order; other vertices
become one singleton boundary leaf per original incidence. -/
noncomputable def coefficientRegions (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) : RibbonMap D :=
  P.withRotation (isolateComplement P.rotation old hold)

@[simp] theorem coefficientRegions_edge (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) : (P.coefficientRegions old hold).edge = P.edge := rfl

open Classical in
@[simp] theorem coefficientRegions_rotation (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) (d : D) :
    (P.coefficientRegions old hold).rotation d = if old d then P.rotation d else d := rfl

/-- All coefficient-region components are planar, including components disconnected by
splitting the retained relator vertices. -/
theorem coefficientRegions_euler [Fintype D] (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) (h : P.EulerEquality) :
    (P.coefficientRegions old hold).EulerEquality :=
  P.splitRefinement_preserves_euler (isolateComplement_refinement P.rotation old hold) h

/-- Original inverse-edge tags and old-vertex factor homogeneity make every actual
coefficient-region component lie in one coefficient factor. -/
theorem coefficientRegions_factor_constant (old : D → Prop)
    (hold : ∀ d, old (P.rotation d) ↔ old d) (tag : D → X)
    (hedge : ∀ d, tag (P.edge d) = tag d)
    (hvertex : ∀ d, old d → tag (P.rotation d) = tag d)
    {d e : D} (h : (P.coefficientRegions old hold).SameComponent d e) : tag d = tag e := by
  induction h with
  | rel x y h =>
    rcases h with h | h
    · rw [← h]
      exact (hedge x).symm
    · rw [← h, coefficientRegions_rotation]
      split
      · exact (hvertex x ‹old x›).symm
      · rfl
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonMap
