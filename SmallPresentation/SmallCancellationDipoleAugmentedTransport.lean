module

public import SmallPresentation.SmallCancellationDipoleAugmentedCoordinates

/-! Transport canonical doubled rows to the general full-row surgery coordinates. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool)
    (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)

/-- The canonical augmented ribbon in ordinary row-word coordinates. -/
noncomputable def markerRibbon :
    RowRibbon (fun o ↦ markerWord length G rows (labels o) (signs o)) where
  map := {
    edge := (markerCoordinates length G rows labels signs).symm.trans
      (P.edge.trans (markerCoordinates length G rows labels signs))
    edge_involutive d := by
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      rw [P.edge_involutive ((markerCoordinates length G rows labels signs).symm d),
        Equiv.apply_symm_apply]
    edge_ne d := by
      intro h
      apply P.edge_ne ((markerCoordinates length G rows labels signs).symm d)
      have hh := congrArg (markerCoordinates length G rows labels signs).symm h
      simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using hh
    rotation := (markerCoordinates length G rows labels signs).symm.trans
      (P.rotation.trans (markerCoordinates length G rows labels signs)) }
  rotation_eq := by
    apply Equiv.ext
    intro d
    change markerCoordinates length G rows labels signs
      (P.rotation ((markerCoordinates length G rows labels signs).symm d)) = _
    rw [hrotation, markerCoordinates_rotation, Equiv.apply_symm_apply]
  edge_letters d := by
    change rowRead _ (markerCoordinates length G rows labels signs
      (P.edge ((markerCoordinates length G rows labels signs).symm d))) = _
    rw [markerCoordinates_read, hedge]
    rw [← markerCoordinates_read length G rows labels signs
      ((markerCoordinates length G rows labels signs).symm d), Equiv.apply_symm_apply]

theorem markerRibbon_edge (d : Darts length labels) :
    (markerRibbon length G rows labels signs P hedge hrotation).map.edge
      (markerCoordinates length G rows labels signs d) =
        markerCoordinates length G rows labels signs (P.edge d) := by
  simp only [markerRibbon, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem markerRibbon_rotation (d : Darts length labels) :
    (markerRibbon length G rows labels signs P hedge hrotation).map.rotation
      (markerCoordinates length G rows labels signs d) =
        markerCoordinates length G rows labels signs (P.rotation d) := by
  simp only [markerRibbon, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem markerRibbon_euler [Finite O] (hE : P.EulerEquality) :
    (markerRibbon length G rows labels signs P hedge hrotation).map.EulerEquality := by
  exact (P.relabel_euler_iff (markerRibbon length G rows labels signs P hedge hrotation).map
    (markerCoordinates length G rows labels signs)
    (fun d ↦ (markerRibbon_edge length G rows labels signs P hedge hrotation d).symm)
    (fun d ↦ (markerRibbon_rotation length G rows labels signs P hedge hrotation d).symm)).mp hE

/-- Relative coefficients transported to the literal flattened marker rows. -/
noncomputable def markerLabelling :
    RibbonLabelling (markerRibbon length G rows labels signs P hedge hrotation).map
      A (Monoid.CoprodI G) where
  arc d := arc length G rows labels signs ((markerCoordinates length G rows labels signs).symm d)
  corner d := corner length G rows labels signs
    ((markerCoordinates length G rows labels signs).symm d)
  edge_arc d := by
    change arc length G rows labels signs ((markerCoordinates length G rows labels signs).symm
      (markerCoordinates length G rows labels signs
        (P.edge ((markerCoordinates length G rows labels signs).symm d)))) = _
    rw [Equiv.symm_apply_apply]
    exact hedge _

theorem markerLabelling_arc (d) :
    (markerLabelling length G rows labels signs P hedge hrotation).arc d =
      rowRead (fun o ↦ markerWord length G rows (labels o) (signs o)) d := by
  exact (markerCoordinates_read length G rows labels signs
    ((markerCoordinates length G rows labels signs).symm d)).symm.trans
      (congrArg _ ((markerCoordinates length G rows labels signs).apply_symm_apply d))

variable {Q : Type} [Group Q] (q : Monoid.CoprodI G →* Q)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)

/-- Flattening retains the complete actual quotient potential. -/
noncomputable def markerPotential :
    CornerPotential (markerLabelling length G rows labels signs P hedge hrotation) q where
  value d := F.value ((markerCoordinates length G rows labels signs).symm d)
  edge d := by
    change F.value ((markerCoordinates length G rows labels signs).symm
      (markerCoordinates length G rows labels signs
        (P.edge ((markerCoordinates length G rows labels signs).symm d)))) = _
    rw [Equiv.symm_apply_apply]
    exact F.edge _
  rotation d := by
    change F.value ((markerCoordinates length G rows labels signs).symm
      (markerCoordinates length G rows labels signs
        (P.rotation ((markerCoordinates length G rows labels signs).symm d)))) = _
    rw [Equiv.symm_apply_apply]
    exact F.rotation _

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
