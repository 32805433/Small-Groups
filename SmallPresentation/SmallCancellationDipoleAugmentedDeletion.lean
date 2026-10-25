module

public import SmallPresentation.SmallCancellationDipoleAugmentedPair

/-!
# Actual full-row deletion in canonical doubled occurrence coordinates

Flatten the markers, perform the proved full-row surgery, and return to the canonical
alternating marker coordinates on precisely the remaining original indices. All original
corner coefficients and quotient path values are retained literally.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A Q : Type} [Finite O] [Group Q]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool) (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)
    (q : Monoid.CoprodI G →* Q)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)

include hrotation in
/-- Concrete deletion of the two matched rows preserves canonical marker readings,
all surviving quotient paths, and spherical Euler characteristic. -/
theorem exists_deletePicture (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hdistinct : first ≠ second) (hlabel : labels first = labels second)
    (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (hanchor : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩)
    (hE : P.EulerEquality) :
    ∃ (P' : RibbonMap (Darts length (fun o : RowDeletion.Remaining first second ↦ labels o.val)))
      (hedge' : ∀ d, arc length G rows (fun o : RowDeletion.Remaining first second ↦ labels o.val) (fun o : RowDeletion.Remaining first second ↦ signs o.val) (P'.edge d) =
        reverseLetter (arc length G rows (fun o : RowDeletion.Remaining first second ↦ labels o.val) (fun o : RowDeletion.Remaining first second ↦ signs o.val) d))
      (_hrotation' : P'.rotation = rotation length (fun o : RowDeletion.Remaining first second ↦ labels o.val))
      (F' : CornerPotential
        (labelling length G rows (fun o : RowDeletion.Remaining first second ↦ labels o.val) (fun o : RowDeletion.Remaining first second ↦ signs o.val) P' hedge') q),
      (∀ (o : RowDeletion.Remaining first second) k b, F'.value ⟨o, k, b⟩ = F.value ⟨o.val, k, b⟩) ∧ P'.EulerEquality := by
  classical
  let D := markerDipole length G rows labels signs P hedge hrotation
    first second k l hdistinct hlabel hsign hposition hanchor
  let T : RowRibbon (fun o : RowDeletion.Remaining first second ↦
      markerWord length G rows (labels o.val) (signs o.val)) := D.delete
  let L := markerLabelling length G rows labels signs P hedge hrotation
  let F₀ := markerPotential length G rows labels signs P hedge hrotation q F
  have hpair := markerDipole_pair_values length G rows labels signs P hedge hrotation q F
    first second k l hdistinct hlabel hsign hposition hanchor
  let F₁ := D.deletePotential L
    (markerLabelling_arc length G rows labels signs P hedge hrotation) F₀ hpair
  let labels' : RowDeletion.Remaining first second → I := fun o ↦ labels o.val
  let signs' : RowDeletion.Remaining first second → Bool := fun o ↦ signs o.val
  let e := markerCoordinates length G rows labels' signs'
  let P' : RibbonMap (Darts length labels') := {
    edge := e.trans (T.map.edge.trans e.symm)
    edge_involutive d := by
      change e.symm (T.map.edge (e (e.symm (T.map.edge (e d))))) = d
      rw [Equiv.apply_symm_apply, T.map.edge_involutive (e d), Equiv.symm_apply_apply]
    edge_ne d := by
      intro h
      apply T.map.edge_ne (e d)
      have hh := congrArg e h
      change e (e.symm (T.map.edge (e d))) = e d at hh
      simpa only [Equiv.apply_symm_apply] using hh
    rotation := rotation length labels' }
  have he (d : Darts length labels') : e (P'.edge d) = T.map.edge (e d) := by
    change e (e.symm (T.map.edge (e d))) = _
    exact e.apply_symm_apply _
  have hr (d : Darts length labels') : e (P'.rotation d) = T.map.rotation (e d) := by
    rw [T.rotation_eq]
    exact markerCoordinates_rotation length G rows labels' signs' d
  have hedge' (d : Darts length labels') : arc length G rows labels' signs' (P'.edge d) =
      reverseLetter (arc length G rows labels' signs' d) := by
    rw [← markerCoordinates_read length G rows labels' signs' (P'.edge d), he,
      T.edge_letters, markerCoordinates_read]
  have hvalue (d : Darts length labels') : F₁.value (e d) = F.value ⟨d.1.val, d.2⟩ := by
    change F.value ((markerCoordinates length G rows labels signs).symm
      (markerCoordinates length G rows labels signs ⟨d.1.val, d.2⟩)) = _
    rw [Equiv.symm_apply_apply]
  have hcorner (d : Darts length labels') :
      (D.deleteLabelling L (markerLabelling_arc length G rows labels signs P hedge hrotation)).corner
        (e d) = corner length G rows labels' signs' d := by
    change corner length G rows labels signs ((markerCoordinates length G rows labels signs).symm
      (markerCoordinates length G rows labels signs ⟨d.1.val, d.2⟩)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  let F' : CornerPotential (labelling length G rows labels' signs' P' hedge') q := {
    value d := F₁.value (e d)
    edge d := by rw [he]; exact F₁.edge (e d)
    rotation d := by
      rw [hr]
      exact (F₁.rotation (e d)).trans (by rw [hcorner]; rfl) }
  refine ⟨P', hedge', rfl, F', ?_, ?_⟩
  · intro o k b
    exact hvalue ⟨o, k, b⟩
  · apply (P'.relabel_euler_iff T.map e he hr).mpr
    exact D.delete_euler (markerRibbon_euler length G rows labels signs P hedge hrotation hE)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
