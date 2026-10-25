module

public import SmallPresentation.PermutationCycleProducts

/-!
# Noncommutative face products with transferred corner coefficients

An adjacent vertex cancellation cuts the face permutation at the predecessor corner and
the following corner. Its inverse corner weights transfer the latter weight to the beginning
of the former. These formulas describe both face merging and face splitting, keeping the
conjugations needed in noncommutative coefficient groups.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

variable {D H : Type*} [Finite D] [Group H] (σ : Equiv.Perm D)

omit [Finite D] in
/-- Replacing weights away from a particular cycle has no effect on its ordered product. -/
theorem cycleProduct_eq_of_agree (v w : D → H) (a : D)
    (h : ∀ d, σ.SameCycle a d → v d = w d) : cycleProduct σ v a = cycleProduct σ w a := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact h _ (Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _))

/-- Changing only the first weight multiplies the based cycle product by the corresponding
left correction factor. -/
theorem cycleProduct_change_start (v w : D → H) (a : D)
    (h : ∀ d, σ.SameCycle a d → d ≠ a → v d = w d) :
    cycleProduct σ v a = v a * (w a)⁻¹ * cycleProduct σ w a := by
  obtain ⟨tail, ht⟩ := cycleBoundary_cons σ a
  have hn := cycleBoundary_nodup σ a
  rw [ht, List.nodup_cons] at hn
  have htail : tail.map v = tail.map w := by
    apply List.map_congr_left
    intro d hd
    apply h d
    · have hm : d ∈ cycleBoundary σ a := by rw [ht]; exact List.mem_cons_of_mem _ hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    · intro he
      exact hn.1 (he ▸ hd)
  simp only [cycleProduct, ht, List.map_cons, List.prod_cons, htail]
  simp [mul_assoc]

open Classical in
/-- Transfer the following corner's inverse weight to the preceding corner at a cut. -/
noncomputable def transferWeight (w : D → H) (a b : D) (d : D) : H :=
  if d = a then w b * w a else if d = b then 1 else w d

/-- On the first of two disjoint cycles, transfer multiplies the product by the other
corner's weight on the left. -/
theorem cycleProduct_transfer_left (w : D → H) (a b : D) (hn : ¬σ.SameCycle a b) :
    cycleProduct σ (transferWeight w a b) a = w b * cycleProduct σ w a := by
  classical
  have hh := cycleProduct_change_start σ (transferWeight w a b) w a (by
    intro d hd hda
    have hdb : d ≠ b := fun he ↦ hn (he ▸ hd)
    simp [transferWeight, hda, hdb])
  simpa [transferWeight, mul_assoc] using hh

/-- On the second of two disjoint cycles, transfer removes its leading weight. -/
theorem cycleProduct_transfer_right (w : D → H) (a b : D) (hn : ¬σ.SameCycle a b) :
    cycleProduct σ (transferWeight w a b) b = (w b)⁻¹ * cycleProduct σ w b := by
  classical
  have hba : b ≠ a := fun he ↦ hn (he ▸ Equiv.Perm.SameCycle.refl σ b)
  have hh := cycleProduct_change_start σ (transferWeight w a b) w b (by
    intro d hd hdb
    have hda : d ≠ a := fun he ↦ hn (he ▸ hd.symm)
    simp [transferWeight, hda, hdb])
  simpa [transferWeight, hba] using hh

/-- Merging two faces after the corner transfer has this exact ordered product. -/
theorem cycleProduct_cut_transfer_merge (w : D → H) (a b : D) (hn : ¬σ.SameCycle a b) :
    cycleProduct (cutAt σ a b) (transferWeight w a b) a =
      w b * cycleProduct σ w a * (w b)⁻¹ * cycleProduct σ w b := by
  rw [cycleProduct_cutAt_merge σ (transferWeight w a b) a b hn,
    cycleProduct_transfer_left σ w a b hn, cycleProduct_transfer_right σ w a b hn]
  simp only [mul_assoc]

/-- Splitting one face gives two new products whose conjugated product is the original.
Neither new product is assumed trivial. -/
theorem cycleProduct_cut_transfer_split (w : D → H) (a b : D) (hne : a ≠ b)
    (hc : σ.SameCycle a b) :
    cycleProduct σ w a =
      (w b)⁻¹ * cycleProduct (cutAt σ a b) (transferWeight w a b) a * w b *
        cycleProduct (cutAt σ a b) (transferWeight w a b) b := by
  have hn := cutAt_not_sameCycle_of_sameCycle σ a b hne hc
  have hh := cycleProduct_cutAt_merge (cutAt σ a b) w a b hn
  rw [cutAt_cutAt] at hh
  rw [cycleProduct_transfer_left (cutAt σ a b) w a b hn,
    cycleProduct_transfer_right (cutAt σ a b) w a b hn]
  simpa [mul_assoc] using hh

/-- A merge of two valid region equations is valid. -/
theorem cut_transfer_merge_eq_one (w : D → H) (a b : D) (hn : ¬σ.SameCycle a b)
    (ha : cycleProduct σ w a = 1) (hb : cycleProduct σ w b = 1) :
    cycleProduct (cutAt σ a b) (transferWeight w a b) a = 1 := by
  rw [cycleProduct_cut_transfer_merge σ w a b hn, ha, hb]
  simp

/-- For a split of a valid face, either new region equation determines the other. This is
used only after a boundary theorem proves the discarded old-only side's equation. -/
theorem cut_transfer_split_eq_one_iff (w : D → H) (a b : D) (hne : a ≠ b)
    (hc : σ.SameCycle a b) (ha : cycleProduct σ w a = 1) :
    cycleProduct (cutAt σ a b) (transferWeight w a b) a = 1 ↔
      cycleProduct (cutAt σ a b) (transferWeight w a b) b = 1 := by
  have hh := cycleProduct_cut_transfer_split σ w a b hne hc
  rw [ha] at hh
  constructor
  · intro h
    simpa [h, mul_assoc] using hh.symm
  · intro h
    rw [h, mul_one] at hh
    have he := congrArg (fun x ↦ w b * x * (w b)⁻¹) hh.symm
    simpa [mul_assoc] using he

omit [Finite D] in
/-- Deleting entries whose weights are one preserves an ordered product in any group. -/
theorem prod_filter_of_trivial_deleted (l : List D) (p : D → Bool) (w : D → H)
    (h : ∀ d ∈ l, p d = false → w d = 1) :
    ((l.filter p).map w).prod = (l.map w).prod := by
  induction l with
  | nil => simp
  | cons d tail ih =>
    have ht := ih (fun e he ↦ h e (List.mem_cons_of_mem _ he))
    cases hp : p d with
    | false => simp [hp, h d (by simp) hp, ht]
    | true => simp [hp, ht]

end SmallPresentationStatements.PermutationCycles
