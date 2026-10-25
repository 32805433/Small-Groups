module

public import SmallPresentation.SmallCancellationDipoleRelativeWeights
public import SmallPresentation.SmallCancellationDipoleRelativeDeletion

/-! Literal flattened marker coordinates for augmented row deletion. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

/-- Interleave the two marker phases in their literal cyclic row order. -/
def markerIndex (n : ℕ) : Fin n × Bool ≃ Fin (2 * n) where
  toFun d := ⟨2 * d.1.val + if d.2 then 1 else 0, by have := d.1.isLt; split <;> omega⟩
  invFun t := (⟨t.val / 2, by have := t.isLt; omega⟩, decide (t.val % 2 = 1))
  left_inv := by
    rintro ⟨k, b⟩
    apply Prod.ext
    · apply Fin.ext
      cases b <;> simp only [Bool.false_eq_true, reduceIte]
      all_goals omega
    · cases b <;> simp
  right_inv := by
    intro t
    apply Fin.ext
    dsimp
    split <;> rename_i h <;> simp only [decide_eq_true_eq] at h
    all_goals omega

@[simp] theorem markerIndex_false (n : ℕ) (k : Fin n) :
    (markerIndex n (k, false)).val = 2 * k.val := by simp [markerIndex]

@[simp] theorem markerIndex_true (n : ℕ) (k : Fin n) :
    (markerIndex n (k, true)).val = 2 * k.val + 1 := rfl

/-- Full marker reversal reverses the syllable index and exchanges its two phases. -/
theorem markerIndex_reverse (n : ℕ) (k : Fin n) (b : Bool) :
    markerIndex n (k.rev, !b) = (markerIndex n (k, b)).rev := by
  apply Fin.ext
  have := k.isLt
  cases b <;> simp only [markerIndex_false, markerIndex_true, Bool.not_false,
    Bool.not_true, Fin.val_rev]
  all_goals omega

variable {O I A : Type} (length : I → ℕ)
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)

/-- The literal marker word of an augmented signed row, with no coefficients erased from
its positional data. -/
def markerWord (i : I) (sign : Bool) : List (SignedLetter A) :=
  List.ofFn (fun t : Fin (2 * length i) ↦
    ((literalSyllable length G rows i sign ((markerIndex (length i)).symm t).1).1,
      !((markerIndex (length i)).symm t).2))

@[simp] theorem markerWord_length (i : I) (sign : Bool) :
    (markerWord length G rows i sign).length = 2 * length i := List.length_ofFn

/-- The flattened positions and the original pair coordinates describe the same full word. -/
def markerPosition (i : I) (sign : Bool) :
    Fin (length i) × Bool ≃ Fin (markerWord length G rows i sign).length :=
  (markerIndex (length i)).trans (finCongr (markerWord_length length G rows i sign).symm)

@[simp] theorem markerPosition_val (i : I) (sign : Bool) (k : Fin (length i)) (b : Bool) :
    (markerPosition length G rows i sign (k, b)).val = 2 * k.val + if b then 1 else 0 := rfl

@[simp] theorem markerWord_read (i : I) (sign : Bool) (d : Fin (length i) × Bool) :
    (markerWord length G rows i sign)[markerPosition length G rows i sign d] =
      ((literalSyllable length G rows i sign d.1).1, !d.2) := by
  simp only [Fin.getElem_fin, markerWord, List.getElem_ofFn]
  change ((literalSyllable length G rows i sign
    ((markerIndex (length i)).symm (markerIndex (length i) d)).1).1,
    !((markerIndex (length i)).symm (markerIndex (length i) d)).2) = _
  rw [Equiv.symm_apply_apply]

/-- Inverse signed occurrences have literally inverse marker words. -/
theorem markerWord_not (i : I) (sign : Bool) :
    markerWord length G rows i (!sign) = FreeGroup.invRev (markerWord length G rows i sign) := by
  apply List.ext_getElem
  · simp
  · intro t ht hs
    have ht' : t < 2 * length i := by simpa using ht
    let z : Fin (2 * length i) := ⟨t, ht'⟩
    let d := (markerIndex (length i)).symm z
    have hz : markerIndex (length i) d = z := (markerIndex _).apply_symm_apply z
    have hrev : (markerIndex (length i)).symm z.rev = (d.1.rev, !d.2) := by
      apply (markerIndex _).injective
      rw [(markerIndex _).apply_symm_apply, markerIndex_reverse, hz]
    have hv := IdentityBoundary.invRev_letter (markerWord length G rows i sign)
      (markerPosition length G rows i sign (d.1.rev, !d.2))
    have hidx : (markerPosition length G rows i sign (d.1.rev, !d.2)).val =
        2 * length i - (t + 1) := by
      change (markerIndex (length i) (d.1.rev, !d.2)).val = _
      rw [markerIndex_reverse, hz]
      rfl
    have hcast : Fin.cast FreeGroup.invRev_length.symm
        (markerPosition length G rows i sign (d.1.rev, !d.2)).rev =
        (⟨t, hs⟩ : Fin (FreeGroup.invRev (markerWord length G rows i sign)).length) := by
      apply Fin.ext
      change (markerWord length G rows i sign).length -
        ((markerPosition length G rows i sign (d.1.rev, !d.2)).val + 1) = t
      have hl := markerWord_length length G rows i sign
      omega
    simp only [hcast, markerWord_read] at hv
    have hh := markerWord_read length G rows i (!sign) d
    have hindex : markerPosition length G rows i (!sign) d = ⟨t, ht⟩ := by
      apply Fin.ext
      exact congrArg (fun x : Fin (2 * length i) ↦ x.val) hz
    simp only [hindex] at hh
    simp only [Fin.getElem_fin] at hh hv
    rw [hh, hv, literalSyllable_not]
    simp only [inverseSyllable, reverseLetter, Bool.not_not]

variable (labels : O → I) (signs : O → Bool)

/-- Actual occurrence-preserving marker coordinates. -/
def markerCoordinates : Darts length labels ≃
    RowDarts (fun o ↦ markerWord length G rows (labels o) (signs o)) :=
  Equiv.sigmaCongrRight (fun o ↦ markerPosition length G rows (labels o) (signs o))

@[simp] theorem markerCoordinates_apply (o : O) (k : Fin (length (labels o))) (b : Bool) :
    markerCoordinates length G rows labels signs ⟨o, k, b⟩ =
      ⟨o, markerPosition length G rows (labels o) (signs o) (k, b)⟩ := rfl

@[simp] theorem markerCoordinates_read (d : Darts length labels) :
    rowRead (fun o ↦ markerWord length G rows (labels o) (signs o))
      (markerCoordinates length G rows labels signs d) = arc length G rows labels signs d := by
  rcases d with ⟨o, k, b⟩
  exact markerWord_read length G rows (labels o) (signs o) (k, b)

variable [∀ i, NeZero (length i)]

/-- Flattening takes the canonical alternating rotation to the ordinary marker row rotation. -/
theorem markerCoordinates_rotation (d : Darts length labels) :
    markerCoordinates length G rows labels signs (rotation length labels d) =
      rowRotation (fun o ↦ markerWord length G rows (labels o) (signs o))
        (markerCoordinates length G rows labels signs d) := by
  rcases d with ⟨o, k, b⟩
  have hk := k.isLt
  cases b <;> apply congrArg (Sigma.mk o) <;> apply Fin.ext
  · change 2 * k.val + 1 =
      (finRotate (markerWord length G rows (labels o) (signs o)).length
        (markerPosition length G rows (labels o) (signs o) (k, false))).val
    rw [PermutationCycles.finRotate_value, markerPosition_val, markerWord_length]
    simp only [Bool.false_eq_true, reduceIte, add_zero]
    rw [Nat.mod_eq_of_lt (by omega)]
  · change 2 * (k + 1).val =
      (finRotate (markerWord length G rows (labels o) (signs o)).length
        (markerPosition length G rows (labels o) (signs o) (k, true))).val
    rw [← finRotate_apply, PermutationCycles.finRotate_value,
      PermutationCycles.finRotate_value, markerPosition_val, markerWord_length]
    simp only [reduceIte]
    by_cases hn : k.val + 1 < length (labels o)
    · rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hn' : k.val + 1 = length (labels o) := by omega
      have ht : 2 * k.val + 1 + 1 = 2 * length (labels o) := by omega
      rw [hn', Nat.mod_self, ht, Nat.mod_self, mul_zero]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
