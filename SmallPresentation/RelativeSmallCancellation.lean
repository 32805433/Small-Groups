module

public import SmallPresentation.SmallCancellationFactorEmbedding
public import SmallPresentation.SmallCancellationIdentityReduction
public import SmallPresentation.RelationTorsionRows

/-!
# Metric small-cancellation consequences

Factor embedding is proved locally by finite marked-picture reduction, using the
metric formulation motivated by Bogley--Pride, Aspherical relative presentations (1992),
Sections 3.3--3.4 and Lemma 3.2.
Weighted identity balance is proved in SmallCancellationIdentityReduction from
factor embedding by actual finite picture surgery. Torsion preservation then follows
from the reusable relation-module cyclic obstruction; no separate reduction is assumed.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]

/-- Metric small cancellation preserves each factor injection, by the locally proved
marked-picture argument. No torsion or homology conclusion is assumed. -/
theorem metric_factor_injective
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    ∀ a, Function.Injective (factorMap G length rows a) := by
  exact factor_injective_of_metric G length rows hidentity hreduced hmetric

/-- The group-ring identity invariant is proved from the factor-embedding input by actual
old-disc erasure and indexed relative dipole deletion. -/
theorem metric_row_weighted_balanced
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    RelationDerivative.CanonicalSchur.RowWeightedBalanced G length rows :=
  metric_row_weighted_balanced_of_factor_injective G length rows hidentity hreduced hmetric
    (metric_factor_injective G length rows hidentity hreduced hmetric)

/-- Torsion preservation is derived from factor embedding and the proved weighted
identity invariant using the full relation-module sequence and cyclic norm obstruction. -/
theorem metric_factor_injection_and_torsion
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    (∀ a, Function.Injective (factorMap G length rows a)) ∧
      ((∀ a, IsMulTorsionFree (G a)) → IsMulTorsionFree (Quotient G length rows)) := by
  have hi := metric_factor_injective G length rows hidentity hreduced hmetric
  refine ⟨hi, ?_⟩
  intro ht
  let := ht
  exact RelationDerivative.CanonicalSchur.rowQuotient_torsionFree_of_weighted G length rows hi
    (metric_row_weighted_balanced G length rows hidentity hreduced hmetric)

/-- The triple-based interface is a corollary of the reusable metric theorem. -/
theorem short_overlap_factor_injection_and_torsion
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows) :
    (∀ a, Function.Injective (factorMap G length rows a)) ∧
      ((∀ a, IsMulTorsionFree (G a)) → IsMulTorsionFree (Quotient G length rows)) := by
  exact metric_factor_injection_and_torsion G length rows hidentity hreduced
    (metric_of_triple_injective G length rows htriple hlength)

end SmallPresentationStatements.RelativeSmallCancellation
