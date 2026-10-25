module

public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces
public import SmallPresentation.SmallCancellationDipoleAugmentedMetric
public import SmallPresentation.SmallCancellationGeometryRelativeRestriction

/-!
# Actual metric dipoles in arbitrary spherical coefficient pictures with embedded factors

Each nonempty connected component inherits the actual sphere equation. Factor embeddings
recover every coefficient-region equation from the quotient paths. The existing metric
curvature theorem then produces an indexed opposite-row edge in that actual component.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadings

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type*} [Fintype D] {P : RibbonMap D}
    {L : RibbonLabelling P A (Monoid.CoprodI G)} (R : AugmentedReadings G length rows P L)

/-- The metric dipole exists in a specified actual component; the original picture may be disconnected. -/
theorem exists_matched_origin_global
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (outside : D) (hregions : ∀ d, L.faceValue d = 1) (heuler : P.EulerEquality) :
    ∃ d, (L.arc d).2 = true ∧ R.origin (P.edge d) = R.origin d := by
  classical
  let p := P.SameComponent outside
  let he := P.component_membership_edge outside
  let hr := P.component_membership_rotation outside
  let R' := R.restrict p he hr
  let a : {d // p d} := ⟨outside, .refl _⟩
  have hf : ∀ d : {d // p d}, (L.restrict p he hr).faceValue d = 1 := by
    intro d
    rw [RibbonLabelling.restrict_faceValue]
    exact hregions d.val
  obtain ⟨d, hd, hm⟩ := R'.exists_matched_origin_of_rows hidentity hreduced hmetric a
    (P.componentRibbon_connected outside) (fun d _ ↦ hf d)
    (P.componentRibbon_sphere heuler outside)
  exact ⟨d.val, hd, hm⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedReadings

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A Q : Type} [Fintype O] [Group Q]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool) (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)
    (q : Monoid.CoprodI G →* Q)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)

include hrotation F in
/-- A finite spherical literal relative picture over embedded factors has an actual indexed dipole. -/
theorem exists_indexed_dipole_of_factor_embeddings
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (hinj : ∀ a, Function.Injective (q.comp (Monoid.CoprodI.of : G a →* _)))
    (outside : Darts length labels) (heuler : P.EulerEquality) :
    ∃ (first second : O) (k : Fin (length (labels first))) (l : Fin (length (labels second))),
      P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩ ∧ first ≠ second ∧
      labels first = labels second ∧ signs second = !signs first ∧
      k.val + l.val + 1 = length (labels first) := by
  have hf := F.faceValue_of_injective_factors G
    (factorCorners length G rows labels signs P hedge hrotation) hinj
  obtain ⟨⟨first, k, b⟩, hb, horigin⟩ :=
    (readings length G rows labels signs P hedge hrotation).exists_matched_origin_global
      hidentity hreduced hmetric outside hf heuler
  cases b with
  | true => contradiction
  | false =>
    obtain ⟨second, l, b, he⟩ : ∃ second l b,
        P.edge ⟨first, k, false⟩ = (⟨second, l, b⟩ : Darts length labels) := by
      rcases P.edge ⟨first, k, false⟩ with ⟨second, l, b⟩
      exact ⟨second, l, b, rfl⟩
    cases b with
    | false =>
      have hh := congrArg Prod.snd (hedge ⟨first, k, false⟩)
      rw [he] at hh
      contradiction
    | true =>
      change origin length labels signs (P.edge ⟨first, k, false⟩) =
        positiveOrigin length (labels first) (signs first) k at horigin
      rw [he] at horigin
      have hm : positiveOrigin length (labels first) (signs first) k =
          negativeOrigin length (labels second) (signs second) l := horigin.symm
      obtain ⟨hne, hlabel, hsign, hpos⟩ :=
        matched_occurrences length labels signs first second k l hm
      exact ⟨first, second, k, l, he, hne, hlabel, hsign, by omega⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
