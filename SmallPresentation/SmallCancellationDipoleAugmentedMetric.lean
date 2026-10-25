module

public import SmallPresentation.SmallCancellationDipoleAugmentedReadings
public import SmallPresentation.SmallCancellationGeometryRelativeCurvature

/-!
# The metric theorem yields actual inverse indexed row corners

For the literal indexed augmented row model, the matched origins supplied by relative
curvature identify distinct original occurrences, equal indexed labels, opposite signs,
and complementary marker positions at the actual edge that the curvature proof finds.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} [Fintype O] (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool)
    (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)

include hrotation in
/-- Curvature provides an actual matching edge between opposite indexed original rows. -/
theorem exists_indexed_dipole
    (hmetric : MetricSmallCancellation G length rows) (outside : Darts length labels)
    (hc : P.Connected) (hred : (labelling length G rows labels signs P hedge).CyclicallyReduced)
    (hregions : ∀ y, ¬P.face.SameCycle outside y →
      (labelling length G rows labels signs P hedge).faceValue y = 1)
    (heuler : Fintype.card P.Vertex + Fintype.card P.Face = Fintype.card P.Edge + 2) :
    ∃ (first second : O) (k : Fin (length (labels first))) (l : Fin (length (labels second))),
      P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩ ∧ first ≠ second ∧
      labels first = labels second ∧ signs second = !signs first ∧
      2 * k.val + (2 * l.val + 1) + 1 = 2 * length (labels first) := by
  obtain ⟨⟨first, k, b⟩, hb, horigin⟩ :=
    (readings length G rows labels signs P hedge hrotation).exists_matched_origin
      hmetric outside hc hred hregions heuler
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
      have hmatch : positiveOrigin length (labels first) (signs first) k =
          negativeOrigin length (labels second) (signs second) l := horigin.symm
      exact ⟨first, second, k, l, he,
        matched_occurrences length labels signs first second k l hmatch⟩

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
