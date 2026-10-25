module

public import SmallPresentation.SmallCancellationGeometryCanonicalErasure
public import SmallPresentation.SmallCancellationDipoleRelativeWeights

/-! The new indexed picture has exactly the selected weighted sum of its original identity. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

variable {A I Q J : Type} [Group Q] (G : A → Type) [∀ a, Group (G a)]
    (q : Monoid.CoprodI G →* Q) (select : I → Option J)
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))

/-- Removing old indices from the sum loses no selected weight. -/
theorem weights_eq_new_sum [Fintype (NewOccurrence G s)] :
    Peiffer.weights (q.comp (FreeProductPresentation.projection G))
        (Sum.elim (fun _ ↦ none) select) s =
      ∑ o : NewOccurrence G s, Peiffer.weight (MonoidHom.id Q) select
        ((q (FreeProductPresentation.projection G s[o.index].1.1), o.row), s[o.index].2) := by
  classical
  rw [Peiffer.weights, ← Fin.sum_univ_fun_getElem]
  symm
  apply Fintype.sum_of_injective NewOccurrence.index NewOccurrence.index_injective
  · intro i hi
    cases hlabel : s[i].1.2 with
    | inl r =>
      simp only [Fin.getElem_fin] at hlabel
      simp [Peiffer.weight, Weighted.generator, hlabel]
    | inr j => exact (hi ⟨⟨i, j, hlabel⟩, rfl⟩).elim
  · intro o
    have hl := o.label
    simp only [Fin.getElem_fin] at hl
    simp only [Peiffer.weight, Fin.getElem_fin, hl, Weighted.generator, Sum.elim_inr,
      MonoidHom.comp_apply, MonoidHom.id_apply]

variable (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hkill : ∀ i, q (relatorValue G length rows i) = 1)
    (paths : WordSection (Syllable G))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)
    (W : OldDiscErasure (oldDiscSystem G length rows paths s hs)
      (augmentedCornerPotential G length rows q hkill paths s hs))

/-- Each erased picture occurrence has its original selected group-ring weight. -/
theorem erased_relativeWeight (o : NewOccurrence G s) :
    relativeWeight length G rows NewOccurrence.row (newOccurrenceSigns G s)
        (erasedMap G length rows q hkill paths s hs W)
        (erasedMap_edge_arc G length rows q hkill paths s hs W) q
        (erasedPotential G length rows q hkill paths s hs W) select o =
      Peiffer.weight (MonoidHom.id Q) select
        ((q (FreeProductPresentation.projection G s[o.index].1.1), o.row), s[o.index].2) := by
  simp only [relativeWeight, quotientBase, erasedPotential_base, newOccurrenceSigns]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
