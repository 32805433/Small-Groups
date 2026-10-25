module

public import SmallPresentation.SmallCancellationGeometryPositiveRefinement
public import SmallPresentation.SmallCancellationDipoleAugmentedCoordinates

/-!
# Two actual vertex orbits in inverse-row replacement coordinates

The first marker circle starts at the positive anchor. The second starts immediately after
the opposite negative anchor, so that the latter is its final negative marker. The complete
embedding retains the actual permutation iterates and requires disjoint original vertex cycles.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

open RelativeSmallCancellation.Geometry.AugmentedOccurrence

/-- Interleaving marker phases gives the literal doubled cyclic order. -/
theorem markerIndex_double_rotate {n : ℕ} (d : Fin n × Bool) :
    markerIndex n (doublePerm (finRotate n) d) = finRotate (2 * n) (markerIndex n d) := by
  rcases d with ⟨k, b⟩
  have hk := k.isLt
  apply Fin.ext
  cases b
  · rw [doublePerm_false, markerIndex_true, finRotate_value, markerIndex_false,
      Nat.mod_eq_of_lt (by omega)]
  · rw [doublePerm_true, markerIndex_false, finRotate_value, finRotate_value, markerIndex_true]
    by_cases hn : k.val + 1 < n
    · rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hn' : k.val + 1 = n := by omega
      have ht : 2 * k.val + 1 + 1 = 2 * n := by omega
      rw [hn', Nat.mod_self, ht, Nat.mod_self, mul_zero]

variable {D : Type*} [Finite D] (σ : Equiv.Perm D) (a : D) {n : ℕ}
    (hperiod : Function.minimalPeriod σ a = 2 * n)

/-- Exact two-phase coordinates on a specified actual vertex cycle. -/
noncomputable def doubleOrbit : Fin n × Bool ≃ {d // σ.SameCycle a d} :=
  (markerIndex n).trans ((finCongr hperiod.symm).trans (orbitEquiv σ a))

@[simp] theorem doubleOrbit_val (k : Fin n) (b : Bool) :
    (doubleOrbit σ a hperiod (k, b)).val = σ^[2 * k.val + if b then 1 else 0] a := by
  change (σ ^ (2 * k.val + if b then 1 else 0)) a = _
  rw [Equiv.Perm.coe_pow]

theorem doubleOrbit_rotation (d : Fin n × Bool) :
    (doubleOrbit σ a hperiod (doublePerm (finRotate n) d)).val =
      σ (doubleOrbit σ a hperiod d).val := by
  change (orbitEquiv σ a (finCongr hperiod.symm
    (markerIndex n (doublePerm (finRotate n) d)))).val = _
  rw [markerIndex_double_rotate, finRotate_finCongr]
  exact orbitEquiv_rotate σ a _

variable (b : D) (hperiod_b : Function.minimalPeriod σ b = 2 * n)

include hperiod_b in
/-- Starting the second circle immediately after its anchor preserves its full period. -/
theorem period_after_anchor : Function.minimalPeriod σ (σ b) = 2 * n := by
  have hh := Function.minimalPeriod_apply_iterate (σ.injective.mem_periodicPts b) 1
  simpa only [Function.iterate_one, hperiod_b] using hh

/-- The two literal phase circles mapped into their original actual vertices. -/
noncomputable def pairOrbitMap : (Fin n ⊕ Fin n) × Bool → D
  | (.inl k, phase) => (doubleOrbit σ a hperiod (k, phase)).val
  | (.inr k, phase) => (doubleOrbit σ (σ b) (period_after_anchor σ b hperiod_b) (k, phase)).val

@[simp] theorem pairOrbitMap_left (k : Fin n) (phase : Bool) :
    pairOrbitMap σ a hperiod b hperiod_b (.inl k, phase) =
      σ^[2 * k.val + if phase then 1 else 0] a := doubleOrbit_val _ _ _ _ _

@[simp] theorem pairOrbitMap_right (k : Fin n) (phase : Bool) :
    pairOrbitMap σ a hperiod b hperiod_b (.inr k, phase) =
      σ^[2 * k.val + (if phase then 1 else 0) + 1] b := by
  rw [pairOrbitMap, doubleOrbit_val, Function.iterate_succ_apply]

theorem pairOrbitMap_left_cycle (k : Fin n) (phase : Bool) :
    σ.SameCycle a (pairOrbitMap σ a hperiod b hperiod_b (.inl k, phase)) :=
  (doubleOrbit σ a hperiod (k, phase)).property

theorem pairOrbitMap_right_cycle (k : Fin n) (phase : Bool) :
    σ.SameCycle b (pairOrbitMap σ a hperiod b hperiod_b (.inr k, phase)) :=
  Equiv.Perm.sameCycle_apply_left.mp
    (doubleOrbit σ (σ b) (period_after_anchor σ b hperiod_b) (k, phase)).property

/-- Distinct actual vertex cycles give an embedding of every marker of both rows. -/
theorem pairOrbitMap_injective (hab : ¬σ.SameCycle a b) :
    Function.Injective (pairOrbitMap σ a hperiod b hperiod_b) := by
  rintro ⟨i | i, p⟩ ⟨j | j, q⟩ h
  · have hh := (doubleOrbit σ a hperiod).injective (Subtype.ext h)
    cases hh
    rfl
  · exact (hab ((pairOrbitMap_left_cycle σ a hperiod b hperiod_b i p).trans
      (h ▸ (pairOrbitMap_right_cycle σ a hperiod b hperiod_b j q)).symm)).elim
  · exact (hab ((pairOrbitMap_left_cycle σ a hperiod b hperiod_b j q).trans
      (h.symm ▸ (pairOrbitMap_right_cycle σ a hperiod b hperiod_b i p)).symm)).elim
  · have hh := (doubleOrbit σ (σ b) (period_after_anchor σ b hperiod_b)).injective
      (Subtype.ext h)
    cases hh
    rfl

/-- The actual indexed embedding used for inverse-row factor-block replacement. -/
noncomputable def pairOrbitEmbedding (hab : ¬σ.SameCycle a b) : (Fin n ⊕ Fin n) × Bool ↪ D :=
  ⟨pairOrbitMap σ a hperiod b hperiod_b, pairOrbitMap_injective σ a hperiod b hperiod_b hab⟩

theorem pairOrbitMap_rotation (d : (Fin n ⊕ Fin n) × Bool) :
    pairOrbitMap σ a hperiod b hperiod_b
      (doublePerm (Equiv.sumCongr (finRotate n) (finRotate n)) d) =
        σ (pairOrbitMap σ a hperiod b hperiod_b d) := by
  rcases d with ⟨k | k, phase⟩
  · cases phase
    · exact doubleOrbit_rotation σ a hperiod (k, false)
    · exact doubleOrbit_rotation σ a hperiod (k, true)
  · cases phase
    · exact doubleOrbit_rotation σ (σ b) (period_after_anchor σ b hperiod_b) (k, false)
    · exact doubleOrbit_rotation σ (σ b) (period_after_anchor σ b hperiod_b) (k, true)

/-- The first positive marker is the original anchor itself. -/
theorem pairOrbitMap_anchor_left [NeZero n] :
    pairOrbitMap σ a hperiod b hperiod_b (.inl 0, false) = a := by
  rw [pairOrbitMap_left]
  rfl

/-- The last negative marker of the second row is precisely the opposite original anchor. -/
theorem pairOrbitMap_anchor_right [NeZero n] :
    pairOrbitMap σ a hperiod b hperiod_b (.inr (0 : Fin n).rev, true) = b := by
  rw [pairOrbitMap_right]
  have hn := NeZero.pos n
  have ht : 2 * ((0 : Fin n).rev).val + (if true then 1 else 0) + 1 = 2 * n := by
    simp only [Fin.val_rev, Fin.val_zero, reduceIte]
    omega
  rw [ht, ← hperiod_b, Function.iterate_minimalPeriod]

include hperiod_b in
omit [Finite D] in
/-- Complementary forward and backward intervals agree on the actual periodic orbit. -/
theorem iterate_eq_inverse_of_period (i j : ℕ) (hij : i + j = 2 * n) :
    σ^[i] b = σ.symm^[j] b := by
  apply σ.injective.iterate j
  rw [← Function.iterate_add_apply]
  have hji : j + i = Function.minimalPeriod σ b := by omega
  rw [hji, Function.iterate_minimalPeriod]
  exact (Function.LeftInverse.iterate (σ.apply_symm_apply) j b).symm

/-- Positive markers of the second row are the inverse preceding corners in the backwards reading. -/
theorem pairOrbitMap_right_false_reverse (k : Fin n) :
    pairOrbitMap σ a hperiod b hperiod_b (.inr k, false) = σ.symm^[2 * k.rev.val + 1] b := by
  rw [pairOrbitMap_right]
  apply iterate_eq_inverse_of_period σ b hperiod_b
  have hk := k.isLt
  simp only [Fin.val_rev, Bool.false_eq_true, reduceIte, add_zero]
  omega

/-- Negative markers of the second row lie at the corresponding backwards even positions. -/
theorem pairOrbitMap_right_true_reverse (k : Fin n) :
    pairOrbitMap σ a hperiod b hperiod_b (.inr k, true) = σ.symm^[2 * k.rev.val] b := by
  rw [pairOrbitMap_right]
  apply iterate_eq_inverse_of_period σ b hperiod_b
  have hk := k.isLt
  simp only [Fin.val_rev, reduceIte]
  omega

/-- The image is exactly the union of the two original vertex cycles. -/
theorem pairOrbitMap_range (d : D) :
    d ∈ Set.range (pairOrbitMap σ a hperiod b hperiod_b) ↔
      σ.SameCycle a d ∨ σ.SameCycle b d := by
  constructor
  · rintro ⟨⟨k | k, phase⟩, rfl⟩
    · exact Or.inl (pairOrbitMap_left_cycle σ a hperiod b hperiod_b k phase)
    · exact Or.inr (pairOrbitMap_right_cycle σ a hperiod b hperiod_b k phase)
  · rintro (ha | hb)
    · obtain ⟨⟨k, phase⟩, h⟩ := (doubleOrbit σ a hperiod).surjective ⟨d, ha⟩
      exact ⟨(.inl k, phase), congrArg Subtype.val h⟩
    · have hb' : σ.SameCycle (σ b) d := Equiv.Perm.sameCycle_apply_left.mpr hb
      obtain ⟨⟨k, phase⟩, h⟩ :=
        (doubleOrbit σ (σ b) (period_after_anchor σ b hperiod_b)).surjective ⟨d, hb'⟩
      exact ⟨(.inr k, phase), congrArg Subtype.val h⟩

/-- The positive anchor predecessor in the second row is the actual inverse rotation of b. -/
theorem pairOrbitMap_anchor_predecessor [NeZero n] :
    pairOrbitMap σ a hperiod b hperiod_b (.inr (0 : Fin n).rev, false) = σ.symm b := by
  rw [pairOrbitMap_right_false_reverse, Fin.rev_rev]
  rfl

end SmallPresentationStatements.PermutationCycles
