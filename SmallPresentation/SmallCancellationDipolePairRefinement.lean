module

public import SmallPresentation.SmallCancellationDipoleSplice
public import SmallPresentation.SmallCancellationGeometryCorridorBlock

/-!
# Splitting the merged opposite rows into their actual matched pairs

Two canonical row circles, spliced at the end of the first and start of the second,
give their concatenated circle. The reverse-position correspondence is obtained by
the proved nested corridor cuts with an empty central word.
-/

@[expose] public section

namespace SmallPresentationStatements.PermutationCycles

open RelativeSmallCancellation.Geometry

def reverseFin (n : ℕ) : Equiv.Perm (Fin n) :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

/-- The two incoming-arrow switches join the two original cyclic row orders. -/
theorem double_rotation_splice (m : ℕ) :
    transport finSumFinEquiv
      (cutAt (Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1)))
        (Sum.inl 0) (Sum.inr 0)) = finRotate ((m + 1) + (m + 1)) := by
  rw [transport_cut]
  have he : transport finSumFinEquiv
      (Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1))) = intervalSplit m m :=
    transport_eq _ _ _ (intervalSplit_intertwines m m)
  rw [he]
  change cutAt (intervalSplit m m) (intervalStartLeft m m) (intervalStartRight m m) = _
  have hs : intervalSplit m m = cutAt (finRotate _)
      (intervalStartLeft m m) (intervalStartRight m m) := by
    classical
    ext d
    simp only [intervalSplit, cutAt_apply, Equiv.trans_apply, Equiv.swap_apply_def]
    split_ifs <;> rfl
  rw [hs, cutAt_cutAt]

def pairedCorridorCoordinates (n : ℕ) : CorridorDart n 0 ≃ Fin (n + n) :=
  (corridorCoordinates n 0).trans (finCongr (by omega))

@[simp] theorem pairedCorridorCoordinates_left (n : ℕ) (d : Fin n) :
    pairedCorridorCoordinates n (.inl d) = finSumFinEquiv (.inl d : Fin n ⊕ Fin n) := by
  apply Fin.ext
  rfl

@[simp] theorem pairedCorridorCoordinates_right (n : ℕ) (d : Fin n) :
    pairedCorridorCoordinates n (.inr (.inr d)) =
      finSumFinEquiv (.inr d : Fin n ⊕ Fin n) := by
  apply Fin.ext
  change n + (0 + d.val) = n + d.val
  omega

/-- The empty-center corridor cuts are exactly the reverse-position row matching. -/
theorem double_pairing_refinement (m : ℕ) :
    SplitRefinement
      (cutAt (Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1)))
        (Sum.inl 0) (Sum.inr 0))
      (RowDeletion.interchange (reverseFin (m + 1))) := by
  let e : Fin (0 + 2 * (m + 1)) ≃ Fin ((m + 1) + (m + 1)) := finCongr (by omega)
  have hc : transport e (finRotate (0 + 2 * (m + 1))) =
      finRotate ((m + 1) + (m + 1)) := transport_eq _ _ _ (finRotate_finCongr _)
  have hh := (corridorPermutation_refinement (m + 1) 0).transport e
  rw [hc, transport_trans] at hh
  have ht := hh.transport (finSumFinEquiv.symm :
    Fin ((m + 1) + (m + 1)) ≃ Fin (m + 1) ⊕ Fin (m + 1))
  have hsource : transport finSumFinEquiv.symm (finRotate ((m + 1) + (m + 1))) =
      cutAt (Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1)))
        (Sum.inl 0) (Sum.inr 0) := by
    rw [← double_rotation_splice m]
    apply Equiv.ext
    intro d
    simp [transport]
  rw [hsource, transport_trans] at ht
  have htarget : transport (((corridorCoordinates (m + 1) 0).trans e).trans
      finSumFinEquiv.symm) (corridorPermutation (m + 1) 0) =
      RowDeletion.interchange (reverseFin (m + 1)) := by
    apply transport_eq
    intro d
    rcases d with d | (d | d)
    · change finSumFinEquiv.symm
        (pairedCorridorCoordinates (m + 1) (.inr (.inr d.rev))) =
        RowDeletion.interchange (reverseFin (m + 1))
          (finSumFinEquiv.symm (pairedCorridorCoordinates (m + 1) (.inl d)))
      simp only [pairedCorridorCoordinates_left, pairedCorridorCoordinates_right,
        Equiv.symm_apply_apply]
      rfl
    · exact Fin.elim0 d
    · change finSumFinEquiv.symm
        (pairedCorridorCoordinates (m + 1) (.inl d.rev)) =
        RowDeletion.interchange (reverseFin (m + 1))
          (finSumFinEquiv.symm (pairedCorridorCoordinates (m + 1) (.inr (.inr d))))
      simp only [pairedCorridorCoordinates_left, pairedCorridorCoordinates_right,
        Equiv.symm_apply_apply]
      rfl
  rw [htarget] at ht
  exact ht

theorem finCycle_commute_rotation {n : ℕ} (k d : Fin n) :
    finCycle k (finRotate n d) = finRotate n (finCycle k d) := by
  let := k.neZero
  simp only [finCycle_apply, finRotate_apply]
  ac_rfl

/-- Opposite cyclic shifts preserve the reverse-position correspondence. -/
theorem shifted_reverse (m : ℕ) (k d : Fin (m + 1)) :
    finCycle k.rev d.rev = (finCycle (finRotate _ k) d).rev := by
  have hl : Fin.last m = (-1 : Fin (m + 1)) := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.coe_neg_one]
  simp only [finCycle_apply, finRotate_apply, ← Fin.last_sub, hl]
  abel

/-- The same actual pair refinement works with any marked anchor on the two row circles. -/
theorem anchored_pairing_refinement {n : ℕ} (k : Fin n) :
    SplitRefinement
      (cutAt (Equiv.sumCongr (finRotate n) (finRotate n))
        (Sum.inl (finRotate n k)) (Sum.inr k.rev))
      (RowDeletion.interchange (reverseFin n)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero k.pos.ne'
  let e := Equiv.sumCongr (finCycle (finRotate (m + 1) k)) (finCycle k.rev)
  have hr : transport e (Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1))) =
      Equiv.sumCongr (finRotate (m + 1)) (finRotate (m + 1)) := by
    apply transport_eq
    intro d
    cases d with
    | inl d => exact congrArg Sum.inl (finCycle_commute_rotation _ d)
    | inr d => exact congrArg Sum.inr (finCycle_commute_rotation _ d)
  have hp : transport e (RowDeletion.interchange (reverseFin (m + 1))) =
      RowDeletion.interchange (reverseFin (m + 1)) := by
    apply transport_eq
    intro d
    cases d with
    | inl d => exact congrArg Sum.inr (shifted_reverse m k d)
    | inr d =>
      change Sum.inl (finCycle (finRotate _ k) d.rev) = Sum.inl (finCycle k.rev d).rev
      apply congrArg Sum.inl
      have hh := congrArg Fin.rev (shifted_reverse m k d.rev)
      simpa only [Fin.rev_rev] using hh.symm
  have hh := (double_pairing_refinement m).transport e
  rw [transport_cut, hr, hp] at hh
  simpa only [e, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finCycle_apply,
    zero_add] using hh

theorem cast_anchored_pairing_refinement {n t : ℕ} (h : n = t) (k : Fin n) :
    SplitRefinement
      (cutAt (Equiv.sumCongr (finRotate n) (finRotate t))
        (Sum.inl (finRotate n k)) (Sum.inr (finCongr h k.rev)))
      (RowDeletion.interchange ((reverseFin n).trans (finCongr h))) := by
  subst t
  exact anchored_pairing_refinement k

end SmallPresentationStatements.PermutationCycles
