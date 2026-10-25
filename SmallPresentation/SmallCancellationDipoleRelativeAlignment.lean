module

public import SmallPresentation.SmallCancellationDipoleRelativeWeights
public import SmallPresentation.SmallCancellationDipoleRelativeSplice

/-!
# Exact coefficient alignment at a matched inverse-row anchor

The opposite marker is the negative marker at the reversed syllable position. Its preceding
corner is the inverse of the original positive coefficient, as an equality in the original
free product. Thus the anchor transfer creates two literal identity corners, without using
only their images in the quotient.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)

omit [∀ i, NeZero (length i)] in
/-- Reverse-position coefficients in opposite literal row words are inverses in the free product. -/
theorem inverse_literal_coefficient (i : I) (sign : Bool) (k l : Fin (length i))
    (hposition : k.val + l.val + 1 = length i) :
    includeSyllable G (literalSyllable length G rows i (!sign) l) =
      (includeSyllable G (literalSyllable length G rows i sign k))⁻¹ := by
  have hl : l.rev = k := by
    apply Fin.ext
    simp only [Fin.rev]
    omega
  rw [literalSyllable_not, hl, include_inverse]

variable (labels : O → I) (signs : O → Bool)

omit [∀ i, NeZero (length i)] in
/-- Aligned opposite occurrence coefficients agree exactly, including the dependent row index. -/
theorem matched_positive_coefficients (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first)) :
    corner length G rows labels signs ⟨second, l, false⟩ =
      (corner length G rows labels signs ⟨first, k, false⟩)⁻¹ := by
  change includeSyllable G (literalSyllable length G rows (labels second) (signs second) l) =
    (includeSyllable G (literalSyllable length G rows (labels first) (signs first) k))⁻¹
  rw [hsign]
  have hh : ∀ (i : I) (h : labels first = i) (l : Fin (length i)),
      k.val + l.val + 1 = length (labels first) →
      includeSyllable G (literalSyllable length G rows i (!signs first) l) =
        (includeSyllable G (literalSyllable length G rows (labels first) (signs first) k))⁻¹ := by
    intro i h
    subst i
    intro l hl
    exact inverse_literal_coefficient length G rows _ _ k l hl
  exact hh _ hlabel l hposition

variable (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)

include hrotation in
/-- The original predecessor of the matched opposite marker carries the exact inverse coefficient. -/
theorem matched_face_coefficient (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (he : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    (labelling length G rows labels signs P hedge).corner (P.face ⟨first, k, false⟩) =
      ((labelling length G rows labels signs P hedge).corner ⟨first, k, false⟩)⁻¹ := by
  rw [RibbonMap.face_apply, he, hrotation]
  exact matched_positive_coefficients length G rows labels signs first second k l
    hlabel hsign hposition

include hrotation in
/-- The two distinguished corners after an actual inverse-row splice are both literally one. -/
theorem matched_splice_corners (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (he : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    let L := P.edgeSpliceLabelling (labelling length G rows labels signs P hedge)
      ⟨first, k, false⟩
    L.corner ⟨first, k, false⟩ = 1 ∧ L.corner (P.face ⟨first, k, false⟩) = 1 := by
  refine ⟨?_, ?_⟩
  · simp only [RibbonMap.edgeSpliceLabelling, ↓reduceIte]
  · exact P.edgeSplice_predecessor_corner _ _
      (matched_face_coefficient length G rows labels signs P hedge hrotation
        first second k l hlabel hsign hposition he)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
