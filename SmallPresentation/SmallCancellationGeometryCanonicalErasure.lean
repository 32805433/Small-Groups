module

public import SmallPresentation.SmallCancellationGeometryCanonicalNewDarts
public import SmallPresentation.SmallCancellationGeometryRibbonTransport

/-! Erasing canonical old relations produces a spherical indexed picture with the original weights. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

variable {A I Q : Type} [Group Q] (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    (q : Monoid.CoprodI G →* Q) (hkill : ∀ i, q (relatorValue G length rows i) = 1)
    (paths : WordSection (Syllable G))
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

variable (W : OldDiscErasure (oldDiscSystem G length rows paths s hs)
    (augmentedCornerPotential G length rows q hkill paths s hs))

noncomputable def erasedCoordinates : Darts length (NewOccurrence.row (G := G) (s := s)) ≃
    W.Dart := (newDartEquiv G length rows s).trans W.newEquiv.symm

omit [∀ i, NeZero (length i)] in
theorem erasedCoordinates_inclusion (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    W.inclusion (erasedCoordinates G length rows q hkill paths s hs W d) =
      newDart G length rows s d :=
  congrArg Subtype.val (W.newEquiv.apply_symm_apply ((newDartEquiv G length rows s) d))

noncomputable abbrev erasedMap :=
  W.map.pullback (erasedCoordinates G length rows q hkill paths s hs W)

theorem erasedMap_rotation :
    (erasedMap G length rows q hkill paths s hs W).rotation =
      rotation length (NewOccurrence.row (G := G) (s := s)) := by
  apply Equiv.ext
  intro d
  apply (erasedCoordinates G length rows q hkill paths s hs W).injective
  apply W.inclusion.injective
  rw [W.map.pullback_rotation, W.rotation, erasedCoordinates_inclusion,
    erasedCoordinates_inclusion, newDart_rotation]

omit [∀ i, NeZero (length i)] in
theorem erasedMap_edge_arc (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    arc length G rows NewOccurrence.row (newOccurrenceSigns G s)
        ((erasedMap G length rows q hkill paths s hs W).edge d) =
      reverseLetter (arc length G rows NewOccurrence.row (newOccurrenceSigns G s) d) := by
  let e := erasedCoordinates G length rows q hkill paths s hs W
  have ha (x) : W.label.arc (e x) =
      arc length G rows NewOccurrence.row (newOccurrenceSigns G s) x := by
    rw [W.arc, erasedCoordinates_inclusion, newDart_arc]
  rw [← ha, W.map.pullback_edge, W.label.edge_arc, ha]

/-- The erased canonical picture keeps the quotient paths of all original attaching rows. -/
noncomputable def erasedPotential : CornerPotential
    (labelling length G rows NewOccurrence.row (newOccurrenceSigns G s)
      (erasedMap G length rows q hkill paths s hs W)
      (erasedMap_edge_arc G length rows q hkill paths s hs W)) q where
  value d := W.potential.value (erasedCoordinates G length rows q hkill paths s hs W d)
  edge d := by rw [W.map.pullback_edge, W.potential.edge]
  rotation d := by
    rw [W.map.pullback_rotation, W.potential.rotation, W.corner,
      erasedCoordinates_inclusion, newDart_corner]
    rfl

theorem erasedPotential_base (o : NewOccurrence G s) :
    (erasedPotential G length rows q hkill paths s hs W).value ⟨o, 0, false⟩ =
      q (FreeProductPresentation.projection G s[o.index].1.1) := by
  change W.potential.value _ = _
  rw [W.value, erasedCoordinates_inclusion]
  change (augmentedCornerPotential G length rows q hkill paths s hs).value
      (discAt (words G length rows) s o.index _, false) = _
  rw [augmentedCornerPotential_at]
  change _ * q (FreeProductPresentation.projection G 1) = _
  rw [map_one, map_one, mul_one]

omit [∀ i, NeZero (length i)] in
theorem erasedMap_euler : (erasedMap G length rows q hkill paths s hs W).EulerEquality :=
  W.map.pullback_euler _ W.euler

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
