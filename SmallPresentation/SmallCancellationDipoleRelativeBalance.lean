module

public import SmallPresentation.SmallCancellationDipoleRelativeExistence
public import SmallPresentation.SmallCancellationDipoleAugmentedDeletion
public import SmallPresentation.SmallCancellationDipoleBookkeeping

/-!
# Weighted identity balance for actual spherical relative pictures over embedded factors

Metric curvature extracts an actual opposite indexed row edge. Concrete full-row deletion
retains every other original row and quotient path. Factor embeddings reconstruct all
region equations after each deletion, so induction on the number of original occurrences
removes all rows and proves that their original group-ring-weighted sum is zero.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {I A Q J : Type} [Group Q] (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (q : Monoid.CoprodI G →* Q) (select : I → Option J)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (hinj : ∀ a, Function.Injective (q.comp (Monoid.CoprodI.of : G a →* _)))

include hidentity hreduced hmetric hinj

private theorem weighted_sum_zero_aux (n : ℕ) :
    ∀ (O : Type) (_ : Fintype O) (labels : O → I) (signs : O → Bool)
      (P : RibbonMap (Darts length labels))
      (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
        reverseLetter (arc length G rows labels signs d))
      (_hrotation : P.rotation = rotation length labels)
      (F : CornerPotential (labelling length G rows labels signs P hedge) q),
      Fintype.card O = n → P.EulerEquality →
      (∑ o, relativeWeight length G rows labels signs P hedge q F select o) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro O inst labels signs P hedge hrotation F hn hE
    classical
    by_cases hO : Nonempty O
    · let o : O := Classical.choice hO
      obtain ⟨first, second, k, l, he, hdistinct, hlabel, hsign, hposition⟩ :=
        exists_indexed_dipole_of_factor_embeddings length G rows labels signs P hedge hrotation q F
          hidentity hreduced hmetric hinj ⟨o, 0, false⟩ hE
      obtain ⟨P', hedge', hrotation', F', hvalue, hE'⟩ :=
        exists_deletePicture length G rows labels signs P hedge hrotation q F
          first second k l hdistinct hlabel hsign hposition he hE
      have hlt : Fintype.card (RowDeletion.Remaining first second) < n := by
        rw [← hn]
        exact RowDeletion.card_remaining_lt first second hdistinct
      have hi := ih _ hlt (RowDeletion.Remaining first second) inferInstance
        (fun r ↦ labels r.val) (fun r ↦ signs r.val) P' hedge' hrotation' F' rfl hE'
      have hw := matched_weight_cancel length G rows labels signs P hedge hrotation q F select
        first second k l hlabel hsign hposition he
      rw [RowDeletion.sum_preserved first second hdistinct _ hw]
      rw [← hi]
      apply Finset.sum_congr rfl
      intro r _
      simp only [relativeWeight, quotientBase, hvalue]
    · have : IsEmpty O := not_nonempty_iff.mp hO
      simp

/-- The signed quotient-based contribution of all original row occurrences is zero. All
hypotheses concern the actual finite ribbon, canonical rows, local paths and factor embeddings. -/
theorem weighted_sum_zero {O : Type} [Fintype O]
    (labels : O → I) (signs : O → Bool) (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)
    (hE : P.EulerEquality) :
    (∑ o, relativeWeight length G rows labels signs P hedge q F select o) = 0 :=
  weighted_sum_zero_aux length G rows q select hidentity hreduced hmetric hinj
    (Fintype.card O) O inferInstance labels signs P hedge hrotation F rfl hE

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
