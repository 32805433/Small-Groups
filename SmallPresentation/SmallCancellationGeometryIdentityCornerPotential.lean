module

public import SmallPresentation.SmallCancellationGeometryCanonicalFactor
public import SmallPresentation.SmallCancellationDipoleIdentityRibbon

/-! Actual quotient path potentials on the augmented canonical identity ribbon. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I Q : Type} [Group Q] (paths : WordSection X) (rows : I → List (SignedLetter X))
    (q : FreeGroup X →* Q) (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1)
    (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)

include hkill in
/-- Cyclically advancing an actual original disc corner traverses its literal letter. -/
theorem relatorRibbon_rotation_potential (d : DiscDarts rows s) :
    discPotential paths rows q s ((relatorRibbon paths rows s h).rotation d) =
      discPotential paths rows q s d * q (letterValue (discRead paths rows s d)) := by
  obtain ⟨i, k, rfl⟩ := exists_discAt rows s d
  have hh := (basedRowRibbon paths rows q hkill s h).rotation_potential ⟨i, k⟩
  change rowPotential (indexedWords rows s) q (fun i ↦ q s[i].1.1)
      (rowRotation (indexedWords rows s) ⟨i, k⟩) =
    rowPotential (indexedWords rows s) q (fun i ↦ q s[i].1.1) ⟨i, k⟩ *
      q (letterValue (rowRead (indexedWords rows s) ⟨i, k⟩)) at hh
  rw [← indexedPotential_coordinates paths rows q hkill s,
    indexedRotation_coordinates, ← indexedPotential_coordinates paths rows q hkill s,
    ← indexedRead_coordinates paths rows s] at hh
  exact hh

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology

variable {A I Q : Type} [Group Q] (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)
    (q : Monoid.CoprodI G →* Q) (hkill : ∀ i, q (relatorValue G length rows i) = 1)

include hkill in
theorem canonical_words_killed (i : OldIndex G ⊕ I) :
    (q.comp (FreeProductPresentation.projection G)) (FreeGroup.mk (words G length rows i)) = 1 := by
  cases i with
  | inl r =>
    change q (FreeProductPresentation.projection G (FreeGroup.mk (oldWord G r))) = 1
    rw [← coefficient_product, oldWord_product, map_one]
  | inr i =>
    change q (FreeProductPresentation.projection G (FreeGroup.mk (newWord G length rows i))) = 1
    rw [newWord_evaluates, projection_rowLift]
    exact hkill i

variable (paths : WordSection (Syllable G))
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

/-- The canonical identity gives concrete relative path potentials, with no assumed equality
between the original conjugators of different row occurrences. -/
noncomputable def augmentedCornerPotential :
    CornerPotential (augmentedData G length rows paths s hs).labelling q := by
  let W := words G length rows
  let qf := q.comp (FreeProductPresentation.projection G)
  let F := discPotential paths W qf s
  let L := augmentedData G length rows paths s hs
  apply L.cornerPotential q F
  · intro d
    have hh := relatorRibbon_edge_potential paths W qf
      (canonical_words_killed G length rows q hkill) s (identity_evaluates G length rows s hs) d
    simpa only [L, F, W, qf, augmentedData, ordinary, coefficient_eq_projection,
      MonoidHom.comp_apply] using hh

  · intro d
    have hh := relatorRibbon_rotation_potential paths W qf
      (canonical_words_killed G length rows q hkill) s (identity_evaluates G length rows s hs) d
    simpa only [L, F, W, qf, augmentedData, ordinary, coefficient_eq_projection,
      MonoidHom.comp_apply] using hh

/-- A leading corner retains the original conjugator followed by the literal row prefix. -/
theorem augmentedCornerPotential_at (i : Fin s.length)
    (d : Fin (orientedWord (words G length rows s[i].1.2) s[i].2).length) :
    (augmentedCornerPotential G length rows q hkill paths s hs).value
        (discAt (words G length rows) s i d, false) =
      q (FreeProductPresentation.projection G s[i].1.1) *
        q (FreeProductPresentation.projection G
          (prefixValue (orientedWord (words G length rows s[i].1.2) s[i].2) d.val)) := by
  change discPotential paths (words G length rows)
      (q.comp (FreeProductPresentation.projection G)) s
        (discAt (words G length rows) s i d) = _
  exact discPotential_at paths (words G length rows)
    (q.comp (FreeProductPresentation.projection G))
    (canonical_words_killed G length rows q hkill) s i d

/-- In particular the distinguished zero corner has precisely the input identity weight. -/
theorem augmentedCornerPotential_zero (i : Fin s.length)
    (hp : 0 < (orientedWord (words G length rows s[i].1.2) s[i].2).length) :
    (augmentedCornerPotential G length rows q hkill paths s hs).value
        (discAt (words G length rows) s i ⟨0, hp⟩, false) =
      q (FreeProductPresentation.projection G s[i].1.1) := by
  rw [augmentedCornerPotential_at]
  change _ * q (FreeProductPresentation.projection G 1) = _
  rw [map_one, map_one, mul_one]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
