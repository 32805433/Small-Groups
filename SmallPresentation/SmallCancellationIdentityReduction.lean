module

public import SmallPresentation.RelationIdentityRows
public import SmallPresentation.SmallCancellationCanonicalBalance

/-!
# Weighted metric identity reduction from embedded factors

The original based-Peiffer old-relator reduction was stronger than any downstream consumer
required. The selected group-ring identity invariant is now proved directly: construct the
canonical spherical identity picture, erase every old factor disc retaining all new rows and
quotient paths, and inductively delete actual indexed metric dipoles. Embedded factors recover
region equations from those paths. No separate picture-reduction admission is used.

This does not assert the stronger based-Peiffer equivalence theorem.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

open RelationCoordinates RelationDerivative.CanonicalSchur Homology

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]
variable (rows : ∀ i, Fin (length i) → Syllable G)

/-- Metric small cancellation and actual factor embeddings imply the full weighted
identity invariant for the canonical free presentation. -/
theorem metric_row_weighted_balanced_of_factor_injective
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows)
    (hfactors : ∀ a, Function.Injective (factorMap G length rows a)) :
    RowWeightedBalanced G length rows := by
  let new := rowLift G length rows
  let q := (presentationEquiv G new).toMonoidHom.comp (baseQuotientMap G new)
  have hkill : ∀ i, q (relatorValue G length rows i) = 1 := by
    intro i
    change presentationEquiv G new (baseQuotientMap G new (relatorValue G length rows i)) = 1
    have hi : baseQuotientMap G new (relatorValue G length rows i) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact Subgroup.subset_normalClosure ⟨i, projection_rowLift G length rows i⟩
    rw [hi, map_one]
  have hinj : ∀ a, Function.Injective (q.comp (Monoid.CoprodI.of : G a →* _)) := by
    intro a
    apply (presentationEquiv G new).injective.comp
    have hr : (fun i ↦ FreeProductPresentation.projection G (rowLift G length rows i)) =
        relatorValue G length rows := funext (projection_rowLift G length rows)
    change Function.Injective ((QuotientGroup.mk' (Subgroup.normalClosure
      (Set.range (fun i ↦ FreeProductPresentation.projection G (rowLift G length rows i))))).comp
        (Monoid.CoprodI.of : G a →* _))
    rw [hr]
    exact hfactors a
  have he : q.comp (FreeProductPresentation.projection G) = quotient G new := by
    ext w
    exact presentationEquiv_quotient_projection G new (FreeGroup.of w)
  have h := Geometry.CanonicalWords.balanced_of_factor_embeddings G length rows q
    (some : I → Option I) hkill hidentity hreduced hmetric hinj
  rw [he] at h
  exact h

end SmallPresentationStatements.RelativeSmallCancellation
