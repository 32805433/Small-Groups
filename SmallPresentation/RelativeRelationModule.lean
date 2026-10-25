module

public import SmallPresentation.RelativeSmallCancellation

/-! Canonical relation coordinates for an arbitrary relative presentation.
The geometric input asserts exponent balance for identity sequences under metric
small cancellation. The passage to a free basis of central relation coinvariants
is proved in `IdentitySequences`, for arbitrary groups and relator families.
No Cohen–Lyndon free-group basis theorem is assumed. -/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)

def centralRelator (i : I) : RelationExtension.Kernel (relatorSubgroup G length rows) :=
  ⟨QuotientGroup.mk' (RelationExtension.commutatorKernel (relatorSubgroup G length rows))
      (relatorValue G length rows i), by
    change QuotientGroup.mk' (relatorSubgroup G length rows) (relatorValue G length rows i) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)⟩

def relationCoordinates : FreeAbelianGroup I →+
    Additive (RelationExtension.Kernel (relatorSubgroup G length rows)) :=
  FreeAbelianGroup.lift (fun i ↦ Additive.ofMul (centralRelator G length rows i))

omit [∀ i, NeZero (length i)] in
@[simp] theorem relationCoordinates_of (i : I) :
    relationCoordinates G length rows (FreeAbelianGroup.of i) =
      Additive.ofMul (centralRelator G length rows i) := FreeAbelianGroup.lift_apply_of _ _

/-- Scalar identity balance follows algebraically from the explicitly isolated
geometric old-relator reduction, via its stronger quotient-weighted invariant. -/
theorem metric_identity_sequences_balanced
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    RelationCoordinates.IdentitySequencesBalanced (relatorValue G length rows) := by
  exact RelationDerivative.CanonicalSchur.row_identity_balanced_of_weighted G length rows
    (metric_row_weighted_balanced G length rows hidentity hreduced hmetric)

/-- Metric small cancellation gives a basis of the central relation coinvariants
by the general identity-sequence algebra, independent of any word construction. -/
theorem metric_relation_coordinates_bijective
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    Function.Bijective (relationCoordinates G length rows) := by
  exact RelationCoordinates.coordinates_bijective_of_identity_sequences
    (relatorValue G length rows)
    (metric_identity_sequences_balanced G length rows hidentity hreduced hmetric)

/-- The concrete triple certificate is only a sufficient criterion for the general theorem. -/
theorem short_overlap_relation_coordinates_bijective
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows) :
    Function.Bijective (relationCoordinates G length rows) := by
  exact metric_relation_coordinates_bijective G length rows hidentity hreduced
    (metric_of_triple_injective G length rows htriple hlength)

noncomputable def relationCoordinatesEquiv
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows) :
    FreeAbelianGroup I ≃+ Additive (RelationExtension.Kernel (relatorSubgroup G length rows)) :=
  AddEquiv.ofBijective (relationCoordinates G length rows)
    (short_overlap_relation_coordinates_bijective G length rows hidentity hreduced hlength htriple)

@[simp] theorem relationCoordinatesEquiv_of
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows) (i : I) :
    relationCoordinatesEquiv G length rows hidentity hreduced hlength htriple
      (FreeAbelianGroup.of i) = Additive.ofMul (centralRelator G length rows i) :=
  relationCoordinates_of G length rows i

end SmallPresentationStatements.RelativeSmallCancellation
