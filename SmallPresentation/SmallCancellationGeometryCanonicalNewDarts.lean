module

public import SmallPresentation.SmallCancellationGeometryCanonicalReadings
public import SmallPresentation.SmallCancellationGeometryOldErasure
public import SmallPresentation.SmallCancellationGeometryIdentityCornerPotential

/-! The retained new incidences are exactly the original indexed signed row coordinates. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))

/-- An original sequence index whose label is a new attaching row. -/
structure NewOccurrence where
  index : Fin s.length
  row : I
  label : s[index].1.2 = Sum.inr row

variable {G s} in
theorem NewOccurrence.index_injective : Function.Injective (NewOccurrence.index (G := G) (s := s)) := by
  rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
  change i = j at h
  subst j
  have hab : a = b := Sum.inr.inj (ha.symm.trans hb)
  subst b
  rfl

instance : Finite (NewOccurrence G s) := Finite.of_injective _ NewOccurrence.index_injective

def newOccurrenceSigns (o : NewOccurrence G s) : Bool := s[o.index].2

/-- The actual inclusion of all doubled new-row coordinates in the initial picture. -/
noncomputable def newDart (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    DiscDarts (words G length rows) s × Bool :=
  newCoordinates G length rows s d.1.index d.1.row d.1.label ⟨(), d.2.1, d.2.2⟩

omit [∀ i, NeZero (length i)] in
theorem newDart_occurrence (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    discOccurrence (words G length rows) s (newDart G length rows s d).1 = d.1.index :=
  discOccurrence_at _ _ _ _

omit [∀ i, NeZero (length i)] in
theorem newDart_new (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    ¬oldIncidence G length rows s (newDart G length rows s d) := by
  rintro ⟨r, hr⟩
  simp only [newDart_occurrence, d.1.label] at hr
  cases hr

omit [∀ i, NeZero (length i)] in
theorem newDart_injective : Function.Injective (newDart G length rows s) := by
  rintro ⟨o, k, b⟩ ⟨p, l, c⟩ h
  have ho := congrArg (fun d ↦ discOccurrence (words G length rows) s d.1) h
  simp only [newDart_occurrence] at ho
  have hop : o = p := NewOccurrence.index_injective ho
  subst p
  have hk := newCoordinates_injective G length rows s o.index o.row o.label h
  have hkl : (k, b) = (l, c) := congrArg (fun d ↦ d.2) hk
  exact congrArg (Sigma.mk o) hkl

/-- This equivalence includes every original new occurrence, even in other components. -/
noncomputable def newDartEquiv : Darts length (NewOccurrence.row (G := G) (s := s)) ≃
    {d : DiscDarts (words G length rows) s × Bool // ¬oldIncidence G length rows s d} :=
  Equiv.ofBijective (fun d ↦ ⟨newDart G length rows s d, newDart_new G length rows s d⟩) (by
    constructor
    · intro d e h
      exact newDart_injective G length rows s (congrArg Subtype.val h)
    · rintro ⟨d, hd⟩
      obtain ⟨i, j, hi, k, he⟩ := new_coordinates_exist G length rows s d hd
      exact ⟨⟨⟨i, j, hi⟩, k, d.2⟩, Subtype.ext he⟩)

variable (paths : WordSection (Syllable G))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

theorem newDart_rotation (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    newDart G length rows s (rotation length NewOccurrence.row d) =
      (ordinary G length rows paths s hs).augmented.rotation (newDart G length rows s d) := by
  rcases d with ⟨o, k, b⟩
  cases b
  · rfl
  · exact newCoordinates_rotation G length rows paths s hs o.index o.row o.label ⟨(), k, true⟩

omit [∀ i, NeZero (length i)] in
theorem newDart_arc (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    (augmentedData G length rows paths s hs).labelling.arc (newDart G length rows s d) =
      arc length G rows NewOccurrence.row (newOccurrenceSigns G s) d :=
  newCoordinates_arc G length rows paths s hs d.1.index d.1.row d.1.label ⟨(), d.2.1, d.2.2⟩

omit [∀ i, NeZero (length i)] in
theorem newDart_corner (d : Darts length (NewOccurrence.row (G := G) (s := s))) :
    (augmentedData G length rows paths s hs).labelling.corner (newDart G length rows s d) =
      corner length G rows NewOccurrence.row (newOccurrenceSigns G s) d :=
  newCoordinates_corner G length rows paths s hs d.1.index d.1.row d.1.label ⟨(), d.2.1, d.2.2⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
