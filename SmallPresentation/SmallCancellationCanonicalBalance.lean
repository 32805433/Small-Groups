module

public import SmallPresentation.SmallCancellationGeometryCanonicalWeights
public import SmallPresentation.SmallCancellationDipoleRelativeBalance

/-! Weighted identities from metric small cancellation and embedded coefficient factors. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology
open AugmentedOccurrence

variable {A I Q J : Type} [Group Q] (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    (q : Monoid.CoprodI G →* Q) (select : I → Option J)
    (hkill : ∀ i, q (relatorValue G length rows i) = 1)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (hinj : ∀ a, Function.Injective (q.comp (Monoid.CoprodI.of : G a →* _)))

include hkill hidentity hreduced hmetric hinj

/-- Every original lifted identity has zero selected quotient-weighted sum. The proof
constructs its picture, erases all old discs, and deletes actual indexed metric dipoles. -/
theorem weights_zero_of_factor_embeddings
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1) :
    Peiffer.weights (q.comp (FreeProductPresentation.projection G))
      (Sum.elim (fun _ ↦ none) select) s = 0 := by
  classical
  let paths := chosenSection (Syllable G)
  let S := oldDiscSystem G length rows paths s hs
  let F := augmentedCornerPotential G length rows q hkill paths s hs
  obtain ⟨W⟩ := OldDiscSystem.exists_erasure _ _ _ S F
    (augmented_euler G length rows paths s hs)
  let : Fintype (NewOccurrence G s) := Fintype.ofFinite _
  have hh := weighted_sum_zero length G rows q select hidentity hreduced hmetric hinj
    NewOccurrence.row (newOccurrenceSigns G s)
    (erasedMap G length rows q hkill paths s hs W)
    (erasedMap_edge_arc G length rows q hkill paths s hs W)
    (erasedMap_rotation G length rows q hkill paths s hs W)
    (erasedPotential G length rows q hkill paths s hs W)
    (erasedMap_euler G length rows q hkill paths s hs W)
  rw [weights_eq_new_sum G q select s]
  simpa only [erased_relativeWeight] using hh

/-- The full group-ring identity invariant, with arbitrary selected new labels and target group. -/
theorem balanced_of_factor_embeddings :
    Weighted.Balanced (all G (rowLift G length rows))
      (q.comp (FreeProductPresentation.projection G)) (Sum.elim (fun _ ↦ none) select) := by
  intro w hw
  induction w using Quot.inductionOn with
  | h s =>
    change Weighted.vector (q.comp (FreeProductPresentation.projection G))
      (Sum.elim (fun _ ↦ none) select) (FreeGroup.mk s) = 1
    apply Multiplicative.toAdd.injective
    rw [Peiffer.vector_mk, weights_zero_of_factor_embeddings G length rows q select hkill
      hidentity hreduced hmetric hinj s ((Peiffer.evaluation_mk _ s).symm.trans hw)]
    rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
