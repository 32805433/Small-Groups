module

public import SmallPresentation.RelatorHomology
public import SmallPresentation.RelativeRelationModule
public import SmallPresentation.FreeProductSchur

/-! The generic relative-aspherical homology consequence used for conversion.
It is separate from the concrete word certificates and from all mitosis calculations. -/
@[expose] public section

open DirectSum

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

theorem presentationKernel_bot_subsingleton (X : Type) :
    Subsingleton (PresentationKernel (⊥ : Subgroup (FreeGroup X))) := by
  have hi : Function.Injective (RelationExtension.projection (⊥ : Subgroup (FreeGroup X))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    unfold RelationExtension.projection
    erw [QuotientGroup.ker_map]
    simp
  constructor
  intro x y
  apply Subtype.ext
  apply Subtype.ext
  apply hi
  exact x.property.trans y.property.symm

theorem free_schur_subsingleton (X : Type) : Subsingleton (Schur (FreeGroup X)) := by
  let := presentationKernel_bot_subsingleton X
  obtain ⟨e⟩ := presentation_kernel_equiv (⊥ : Subgroup (FreeGroup X))
  let f := e.trans (schurEquiv (QuotientGroup.quotientBot : FreeGroup X ⧸ (⊥ : Subgroup (FreeGroup X)) ≃* FreeGroup X))
  exact f.symm.injective.subsingleton

theorem free_schur_torsionFree (X : Type) : IsMulTorsionFree (Schur (FreeGroup X)) := by
  let := free_schur_subsingleton X
  infer_instance

theorem cyclic_schur_torsionFree : IsMulTorsionFree (Schur (Multiplicative ℤ)) := by
  let := free_schur_torsionFree Unit
  let e := schurEquiv (FreeGroup.mulEquivIntOfUnique (α := Unit))
  exact e.symm.injective.isMulTorsionFree e.symm.toMonoidHom

/-- The elementary torsion argument for an exact sequence of abelian groups. -/
theorem uniqueDiv_of_exact {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [HasUniqueDiv A] [HasUniqueDiv C] (i : A →+ B) (hi : Function.Injective i)
    (d : B →+ C) (hexact : d.ker = i.range) : HasUniqueDiv B where
  nsmul_right_injective n hn x y h := by
    change n • x = n • y at h
    have hd : d x = d y := nsmul_right_injective hn (by simpa using congrArg d h)
    have hz : x - y ∈ i.range := by rw [← hexact]; change d (x-y) = 0; simp [hd]
    obtain ⟨z,hz⟩ := hz
    have hnz : n • z = 0 := hi (by rw [map_nsmul, hz, nsmul_sub, h, sub_self, map_zero])
    have hz0 : z = 0 := nsmul_right_injective hn (by simpa using hnz)
    exact sub_eq_zero.mp (by simpa [hz0] using hz.symm)

theorem directSum_uniqueDiv {A : Type} (G : A → Type) [∀ a, Group (G a)]
    (h : ∀ a, IsMulTorsionFree (Schur (G a))) : HasUniqueDiv (⨁ a, H₂ (G a)) := by
  let : ∀ a, IsMulTorsionFree (Schur (G a)) := h
  let : ∀ a, HasUniqueDiv (H₂ (G a)) := fun a ↦
    { nsmul_right_injective := fun _n hn x y hxy ↦
        IsAddTorsionFree.eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all x y) hxy }
  let c : (⨁ a, H₂ (G a)) →+ (∀ a, H₂ (G a)) :=
    { toFun := fun x ↦ x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact Function.Injective.hasUniqueDiv c (fun x y h ↦ DFinsupp.ext (fun a ↦ congrFun h a))

theorem freeAbelian_uniqueDiv (I : Type) : HasUniqueDiv (FreeAbelianGroup I) := by
  let e := FreeAbelianGroup.equivFinsupp I
  let c : FreeAbelianGroup I →+ (I → ℤ) :=
    { toFun := fun x ↦ e x
      map_zero' := by funext i; exact congrFun (congrArg DFunLike.coe e.map_zero) i
      map_add' := fun x y ↦ by funext i; exact congrFun (congrArg DFunLike.coe (e.map_add x y)) i }
  apply Function.Injective.hasUniqueDiv c
  intro x y h
  apply e.injective
  exact Finsupp.ext (fun i ↦ congrFun h i)

end SmallPresentationStatements.Homology

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]

/-- The actual quotient map is injective on the Schur multiplier, by the proved
relation-module detector theorem. Its geometric dependencies are factor injection
and weighted identity balance, both proved by finite ribbon surgery. -/
theorem metric_schur_injective
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    Function.Injective (Homology.map₂ (QuotientGroup.mk' (relatorSubgroup G length rows))) := by
  exact RelationDerivative.CanonicalSchur.map₂_rowQuotient_injective_of_weighted
    G length rows
    (metric_factor_injective G length rows hidentity hreduced hmetric)
    (metric_row_weighted_balanced G length rows hidentity hreduced hmetric)

/-- The specified sum of the maps induced by the actual factor inclusions. -/
noncomputable def factorSchurMap (rows : ∀ i, Fin (length i) → Syllable G) :
    (⨁ a, Homology.H₂ (G a)) →+ Homology.H₂ (Quotient G length rows) :=
  (Homology.map₂ (QuotientGroup.mk' (relatorSubgroup G length rows))).comp
    (Homology.freeProductSchurMap G)

omit [∀ i, NeZero (length i)] in
open Classical in
@[simp] theorem factorSchurMap_of (rows : ∀ i, Fin (length i) → Syllable G)
    (a : A) (x : Homology.H₂ (G a)) :
    factorSchurMap G length rows (DirectSum.of (fun a ↦ Homology.H₂ (G a)) a x) =
      Homology.map₂ (factorMap G length rows a) x := by
  simp only [factorSchurMap, AddMonoidHom.comp_apply, Homology.freeProductSchurMap_of,
    Homology.map₂_comp]
  rfl

/-- The canonical quotient transgression in the attaching-relator coordinates. -/
noncomputable def metricTransgression
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    Homology.H₂ (Quotient G length rows) →+ FreeAbelianGroup I :=
  Homology.relatorTransgression (relatorValue G length rows)
    (metric_identity_sequences_balanced G length rows hidentity hreduced hmetric)

/-- The complete low-degree sequence for a metric small-cancellation presentation.
The first map is the sum of the actual factor maps; the relator boundary sends
each attaching row to its abelianization in the free product. -/
theorem metric_homology_exact
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hmetric : MetricSmallCancellation G length rows) :
    Function.Injective (factorSchurMap G length rows) ∧
      (metricTransgression G length rows hidentity hreduced hmetric).ker =
        (factorSchurMap G length rows).range ∧
      (Homology.relatorBoundary (relatorValue G length rows)).ker =
        (metricTransgression G length rows hidentity hreduced hmetric).range ∧
      (Homology.map₁ (QuotientGroup.mk' (relatorSubgroup G length rows))).ker =
        (Homology.relatorBoundary (relatorValue G length rows)).range ∧
      Function.Surjective
        (Homology.map₁ (QuotientGroup.mk' (relatorSubgroup G length rows))) := by
  let h := metric_identity_sequences_balanced G length rows hidentity hreduced hmetric
  refine ⟨(metric_schur_injective G length rows hidentity hreduced hmetric).comp
      (Homology.freeProductSchurMap_injective G), ?_,
    Homology.relatorBoundary_ker _ h, Homology.relator_abelian_ker _,
    RelationExtension.abelianQuotient_surjective _⟩
  change (Homology.relatorTransgression (relatorValue G length rows) h).ker = _
  rw [Homology.relatorTransgression_ker]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := Homology.freeProductSchurMap_surjective G x
    exact ⟨y, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨Homology.freeProductSchurMap G x, rfl⟩

/-- The original short-overlap segment is a specialization of the full canonical sequence. -/
theorem short_overlap_schur_exact
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows) :
    ∃ (i : (⨁ a, Homology.H₂ (G a)) →+ Homology.H₂ (Quotient G length rows))
      (d : Homology.H₂ (Quotient G length rows) →+ FreeAbelianGroup I),
      Function.Injective i ∧ d.ker = i.range := by
  let hm := metric_of_triple_injective G length rows htriple hlength
  obtain ⟨hi, hd, _⟩ := metric_homology_exact G length rows hidentity hreduced hm
  exact ⟨factorSchurMap G length rows,
    metricTransgression G length rows hidentity hreduced hm, hi, hd⟩

/-- Torsion-freeness is a proved consequence of the general exact segment. -/
theorem short_overlap_schur_torsionFree
    (rows : ∀ i, Fin (length i) → Syllable G)
    (hidentity : ∀ i p, (rows i p).2 ≠ 1)
    (hreduced : ∀ i p, (rows i p).1 ≠ (rows i (p + 1)).1)
    (hlength : ∀ i, 19 ≤ length i)
    (htriple : TripleInjective G length rows)
    (hfactor : ∀ a, IsMulTorsionFree (Homology.Schur (G a))) :
    IsMulTorsionFree (Homology.Schur (Quotient G length rows)) := by
  obtain ⟨i,d,hi,hd⟩ := short_overlap_schur_exact G length rows hidentity hreduced hlength htriple
  let := Homology.directSum_uniqueDiv G hfactor
  let := Homology.freeAbelian_uniqueDiv I
  let := Homology.uniqueDiv_of_exact i hi d hd
  exact (inferInstance : IsMulTorsionFree (Multiplicative (Homology.H₂ (Quotient G length rows))))

end SmallPresentationStatements.RelativeSmallCancellation
