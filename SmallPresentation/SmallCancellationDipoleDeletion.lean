module

public import SmallPresentation.SmallCancellationDipoleRibbon

/-!
# Actual deletion of two matched relator rows

All incidences of the two opposite rows are paired in reverse order and suppressed as
finite alternating bands. The surviving occurrence indices, row words, cyclic rotations,
quotient basepoints and edge-potential equations are preserved. This is a concrete finite
operation on based ribbons; no planarity or Euler-preservation assertion is built into it.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole

variable {O X Q : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} {P : BasedRowRibbon words q} (D : P.Dipole)

abbrev Remaining := RowDeletion.Remaining D.first D.second

abbrev RemainingWords : D.Remaining → List (SignedLetter X) := fun o ↦ words o.val

abbrev CutDarts := RowDarts D.RemainingWords ⊕
  (Fin (words D.first).length ⊕ Fin (words D.second).length)

noncomputable def coordinates : D.CutDarts ≃ RowDarts words :=
  RowDeletion.coordinates (fun o ↦ Fin (words o).length) D.first D.second D.distinct

@[simp] theorem coordinates_remaining (d : RowDarts D.RemainingWords) :
    D.coordinates (.inl d) = ⟨d.1.val, d.2⟩ := rfl

@[simp] theorem coordinates_first (d : Fin (words D.first).length) :
    D.coordinates (.inr (.inl d)) = ⟨D.first, d⟩ := rfl

@[simp] theorem coordinates_second (d : Fin (words D.second).length) :
    D.coordinates (.inr (.inr d)) = ⟨D.second, d⟩ := rfl

/-- Pair all removed row corners and fix exactly the surviving row corners. -/
def corridor : Equiv.Perm D.CutDarts := RowDeletion.corridor (inverseCorner D.inverse_words)

/-- The original edges in the new incidence coordinates. -/
noncomputable def cap : Equiv.Perm D.CutDarts :=
  D.coordinates.trans (P.map.edge.trans D.coordinates.symm)

theorem cap_coordinates (d : D.CutDarts) : D.coordinates (D.cap d) = P.map.edge (D.coordinates d) := by
  simp only [cap, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem cap_involutive : Function.Involutive D.cap := by
  intro d
  apply D.coordinates.injective
  rw [D.cap_coordinates, D.cap_coordinates, P.map.edge_involutive]

theorem corridor_involutive : Function.Involutive D.corridor :=
  RowDeletion.corridor_involutive (inverseCorner D.inverse_words)

theorem corridor_fixed_iff (d : D.CutDarts) :
    D.corridor d = d ↔ ∃ r, d = Sum.inl r :=
  RowDeletion.corridor_fixed_iff (inverseCorner D.inverse_words) d

/-- The discarded row correspondence reverses all original edge letters. -/
theorem corridor_letters (d : D.CutDarts) (hd : D.corridor d ≠ d) :
    rowRead words (D.coordinates (D.corridor d)) = reverseLetter (rowRead words (D.coordinates d)) := by
  rcases d with d | (d | d)
  · exact (hd rfl).elim
  · exact inverseCorner_letter D.inverse_words d
  · have hh := inverseCorner_letter D.inverse_words ((inverseCorner D.inverse_words).symm d)
    simp only [Equiv.apply_symm_apply] at hh
    change (words D.first)[(inverseCorner D.inverse_words).symm d] =
      reverseLetter (words D.second)[d]
    simpa only [reverseLetter_reverseLetter] using (congrArg reverseLetter hh).symm

/-- The original quotient potential on these same actual incidences. -/
noncomputable def potential (d : D.CutDarts) : Q := rowPotential words q P.base (D.coordinates d)

theorem cap_potential (d : D.CutDarts) :
    D.potential (D.cap d) = D.potential d * q (letterValue (rowRead words (D.coordinates d))) := by
  rw [potential, D.cap_coordinates]
  exact P.edge_paths _

/-- The correspondence across the removed rows satisfies the corridor path law at every corner. -/
theorem corridor_potential (d : D.CutDarts) (hd : D.corridor d ≠ d) :
    D.potential (D.corridor d) = D.potential d * q (letterValue (rowRead words (D.coordinates d))) := by
  rcases d with d | (d | d)
  · exact (hd rfl).elim
  · exact D.inverse_corner_potential d
  · have hh := D.inverse_corner_potential ((inverseCorner D.inverse_words).symm d)
    rw [Equiv.apply_symm_apply] at hh
    have hl := inverseCorner_letter D.inverse_words ((inverseCorner D.inverse_words).symm d)
    simp only [Equiv.apply_symm_apply] at hl
    change rowPotential words q P.base ⟨D.first, (inverseCorner D.inverse_words).symm d⟩ =
      rowPotential words q P.base ⟨D.second, d⟩ * q (letterValue (words D.second)[d])
    rw [hl, letterValue_reverse, map_inv, hh, mul_assoc, mul_inv_cancel, mul_one]

/-- The dipole deletion is an actual two-involution band system. -/
noncomputable def deletionBands : BandSystem D.CutDarts X where
  cap := D.cap
  corridor := D.corridor
  cap_involutive := D.cap_involutive
  corridor_involutive := D.corridor_involutive
  letter d := rowRead words (D.coordinates d)
  cap_letter d := by rw [D.cap_coordinates]; exact P.edge_letters _
  corridor_letter := D.corridor_letters

/-- Exactly the remaining row corners are endpoints of the deletion bands. -/
noncomputable def retainedEndpoints : RowDarts D.RemainingWords ≃ D.deletionBands.Endpoint :=
  Equiv.ofBijective (fun d ↦ ⟨Sum.inl d, rfl⟩) (by
    constructor
    · intro d e h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · intro d
      obtain ⟨r, hr⟩ := (D.corridor_fixed_iff d.val).mp d.property
      exact ⟨r, Subtype.ext hr.symm⟩)

theorem retainedEndpoints_symm (d : D.deletionBands.Endpoint) :
    Sum.inl (D.retainedEndpoints.symm d) = d.val :=
  congrArg Subtype.val (D.retainedEndpoints.apply_symm_apply d)

variable [Finite O]

/-- The actual edge pairing after deleting the two rows and reconnecting their incident bands. -/
noncomputable def deletedEdge : Equiv.Perm (RowDarts D.RemainingWords) :=
  D.retainedEndpoints.trans (D.deletionBands.endpointPairing.trans D.retainedEndpoints.symm)

theorem deletedEdge_involutive : Function.Involutive D.deletedEdge := by
  intro d
  apply D.retainedEndpoints.injective
  simp only [deletedEdge, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact D.deletionBands.endpoint_involutive _

theorem deletedEdge_ne (d : RowDarts D.RemainingWords) : D.deletedEdge d ≠ d := by
  intro h
  have he := congrArg D.retainedEndpoints h
  simp only [deletedEdge, Equiv.trans_apply, Equiv.apply_symm_apply] at he
  exact D.deletionBands.endpoint_ne _ he

theorem deletedEdge_letters (d : RowDarts D.RemainingWords) :
    rowRead D.RemainingWords (D.deletedEdge d) = reverseLetter (rowRead D.RemainingWords d) := by
  have hh := D.deletionBands.endpoint_letter (D.retainedEndpoints d)
  have he := D.retainedEndpoints_symm (D.deletionBands.endpoint (D.retainedEndpoints d))
  change rowRead words (D.coordinates (Sum.inl
    (D.retainedEndpoints.symm (D.deletionBands.endpoint (D.retainedEndpoints d))))) = _
  rw [he]
  exact hh

theorem deletedEdge_potential (d : RowDarts D.RemainingWords) :
    rowPotential D.RemainingWords q (fun o ↦ P.base o.val) (D.deletedEdge d) =
      rowPotential D.RemainingWords q (fun o ↦ P.base o.val) d *
        q (letterValue (rowRead D.RemainingWords d)) := by
  have hh := D.deletionBands.endpoint_potential (fun x ↦ q (letterValue x))
    (fun x ↦ by rw [letterValue_reverse, map_inv]) D.potential D.cap_potential
    D.corridor_potential (D.retainedEndpoints d)
  have he := D.retainedEndpoints_symm (D.deletionBands.endpoint (D.retainedEndpoints d))
  change D.potential (Sum.inl
    (D.retainedEndpoints.symm (D.deletionBands.endpoint (D.retainedEndpoints d)))) = _
  rw [he]
  exact hh

/-- Delete a genuine dipole, retaining every other row and its original quotient basepoint. -/
noncomputable def delete : BasedRowRibbon D.RemainingWords q where
  map := {
    edge := D.deletedEdge
    edge_involutive := D.deletedEdge_involutive
    edge_ne := D.deletedEdge_ne
    rotation := rowRotation D.RemainingWords
  }
  rotation_eq := rfl
  base o := P.base o.val
  row_killed o := P.row_killed o.val
  edge_letters := D.deletedEdge_letters
  edge_paths := D.deletedEdge_potential

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BasedRowRibbon.Dipole
