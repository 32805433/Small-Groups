module

public import SmallPresentation.SmallCancellationDipoleAugmentedTransport

/-! The actual relative metric dipole as a full marker-row dipole with matched potentials. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool)
    (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)

omit [∀ i, NeZero (length i)] in
/-- Complementary doubled marker positions are the literal inverse-word correspondence. -/
theorem inverse_markerPosition (first second : O)
    (hword : markerWord length G rows (labels second) (signs second) =
      FreeGroup.invRev (markerWord length G rows (labels first) (signs first)))
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hposition : k.val + l.val + 1 = length (labels first)) (b : Bool) :
    BasedRowRibbon.inverseCorner (words := fun o ↦ markerWord length G rows (labels o) (signs o))
      hword (markerPosition length G rows (labels first) (signs first) (k, b)) =
        markerPosition length G rows (labels second) (signs second) (l, !b) := by
  apply Fin.ext
  simp only [BasedRowRibbon.inverseCorner_val, markerPosition_val, markerWord_length]
  cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, reduceIte]
  all_goals omega

/-- The genuine positive-to-negative anchor produces the full row-deletion datum. -/
noncomputable def markerDipole (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hdistinct : first ≠ second) (hlabel : labels first = labels second)
    (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (hanchor : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    (markerRibbon length G rows labels signs P hedge hrotation).Dipole where
  first := first
  second := second
  distinct := hdistinct
  inverse_words := by rw [← hlabel, hsign, markerWord_not]
  anchor := markerPosition length G rows (labels first) (signs first) (k, false)
  edge_anchor := by
    change (markerRibbon length G rows labels signs P hedge hrotation).map.edge
      (markerCoordinates length G rows labels signs ⟨first, k, false⟩) = _
    rw [markerRibbon_edge, hanchor]
    apply congrArg (Sigma.mk second)
    exact (inverse_markerPosition length G rows labels signs first second _ k l hposition false).symm

variable {Q : Type} [Group Q] (q : Monoid.CoprodI G →* Q)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)

@[simp] theorem markerPotential_at (o : O) (k : Fin (length (labels o))) (b : Bool) :
    (markerPotential length G rows labels signs P hedge hrotation q F).value
      ⟨o, markerPosition length G rows (labels o) (signs o) (k, b)⟩ =
        F.value ⟨o, k, b⟩ := by
  change F.value ((markerCoordinates length G rows labels signs).symm
    (markerCoordinates length G rows labels signs ⟨o, k, b⟩)) = _
  rw [Equiv.symm_apply_apply]

/-- The full deleted marker matching has equal relative quotient potentials. -/
theorem markerDipole_pair_values (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hdistinct : first ≠ second) (hlabel : labels first = labels second)
    (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (hanchor : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    let D := markerDipole length G rows labels signs P hedge hrotation
      first second k l hdistinct hlabel hsign hposition hanchor
    ∀ t : Fin (markerWord length G rows (labels first) (signs first)).length,
      (markerPotential length G rows labels signs P hedge hrotation q F).value
        ⟨D.second, BasedRowRibbon.inverseCorner
          (words := fun o ↦ markerWord length G rows (labels o) (signs o)) D.inverse_words t⟩ =
      (markerPotential length G rows labels signs P hedge hrotation q F).value ⟨D.first, t⟩ := by
  dsimp only [markerDipole]
  intro t
  let d := (markerPosition length G rows (labels first) (signs first)).symm t
  have ht : markerPosition length G rows (labels first) (signs first) d = t :=
    (markerPosition _ _ _ _ _).apply_symm_apply t
  have hlen := congrArg length hlabel
  let j : Fin (length (labels second)) := ⟨length (labels first) - (d.1.val + 1), by
    have := d.1.isLt
    omega⟩
  have hj : d.1.val + j.val + 1 = length (labels first) := by
    dsimp [j]
    have := d.1.isLt
    omega
  have hbase := matched_base_eq length G rows labels signs P hedge hrotation q F
    first second k l hlabel hsign hposition hanchor
  rw [← ht]
  have hw : markerWord length G rows (labels second) (signs second) =
      FreeGroup.invRev (markerWord length G rows (labels first) (signs first)) := by
    rw [← hlabel, hsign, markerWord_not]
  change (markerPotential length G rows labels signs P hedge hrotation q F).value
    ⟨second, BasedRowRibbon.inverseCorner
      (words := fun o ↦ markerWord length G rows (labels o) (signs o)) hw
      (markerPosition length G rows (labels first) (signs first) (d.1, d.2))⟩ =
    (markerPotential length G rows labels signs P hedge hrotation q F).value
      ⟨first, markerPosition length G rows (labels first) (signs first) (d.1, d.2)⟩
  rw [inverse_markerPosition length G rows labels signs first second hw d.1 j hj d.2,
    markerPotential_at, markerPotential_at]
  exact (matched_all_marker_values length G rows labels signs P hedge hrotation q F
    first second d.1 j hlabel hsign hj hbase d.2).symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
