module

public import SmallPresentation.Homology

/-!
# The canonical exact sequence of a relation extension

For every normal subgroup `N` of a group `F`, the central relation extension
`F/[N,F]` maps to `F`'s abelianization. Its kernel is its derived subgroup.
Restriction to `N/[N,F]` gives the canonical relation boundary, followed by
the surjection to the abelianization of `F/N`. For a free `F`, the kernel of
the relation boundary is precisely the Hopf presentation kernel.

These statements require neither small cancellation nor an asphericity hypothesis.
-/
@[expose] public section

namespace SmallPresentationStatements.RelationExtension

open scoped commutatorElement

variable {F : Type} [Group F] (N : Subgroup F) [N.Normal]

/-- The central relation quotient still maps canonically to the original abelianization. -/
def abelianProjection : Total N →* Abelianization F :=
  QuotientGroup.lift _ Abelianization.of (by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mpr
    exact (Subgroup.commutator_mono le_top le_rfl) hx)

@[simp] theorem abelianProjection_mk (x : F) :
    abelianProjection N (QuotientGroup.mk' (commutatorKernel N) x) =
      Abelianization.of x := rfl

/-- Abelianizing before or after killing `[N,F]` has the same kernel. -/
theorem abelianProjection_ker : (abelianProjection N).ker = commutator (Total N) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutatorKernel N) x
    have hy : y ∈ commutator F := (QuotientGroup.eq_one_iff y).mp hx
    rw [← map_commutator_of_surjective
      (QuotientGroup.mk'_surjective (commutatorKernel N))]
    exact ⟨y, hy, rfl⟩
  · exact Abelianization.commutator_subset_ker _

/-- The boundary records the abelianized value of a relation. -/
def boundary : Kernel N →* Abelianization F :=
  (abelianProjection N).comp (Kernel N).subtype

/-- The quotient homomorphism on abelianizations. -/
def abelianQuotient : Abelianization F →* Abelianization (F ⧸ N) :=
  Abelianization.map (QuotientGroup.mk' N)

theorem abelianQuotient_surjective : Function.Surjective (abelianQuotient N) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator (F ⧸ N)) x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
  exact ⟨Abelianization.of z, rfl⟩

theorem boundary_comp_abelianQuotient :
    (abelianQuotient N).comp (boundary N) = 1 := by
  ext x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (commutatorKernel N) x.val
  have hx : QuotientGroup.mk' N y = 1 := by
    rw [← projection_mk, hy]
    exact x.property
  change abelianQuotient N (abelianProjection N x.val) = 1
  rw [← hy]
  change Abelianization.of (QuotientGroup.mk' N y) = 1
  rw [hx, map_one]

/-- Exactness at the abelianization of the original group, for every normal subgroup. -/
theorem abelianQuotient_ker : (abelianQuotient N).ker = (boundary N).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (commutator F) x
    have hy : QuotientGroup.mk' N y ∈ commutator (F ⧸ N) :=
      (QuotientGroup.eq_one_iff _).mp hx
    rw [← map_commutator_of_surjective (QuotientGroup.mk'_surjective N)] at hy
    obtain ⟨z, hz, heq⟩ := hy
    have hrel : QuotientGroup.mk' N (y * z⁻¹) = 1 := by
      rw [map_mul, map_inv, heq, mul_inv_cancel]
    refine ⟨⟨QuotientGroup.mk' (commutatorKernel N) (y * z⁻¹), hrel⟩, ?_⟩
    change Abelianization.of (y * z⁻¹) = Abelianization.of y
    have hz' : Abelianization.of z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    simp only [map_mul, map_inv, hz', inv_one, mul_one]
  · rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun (boundary_comp_abelianQuotient N) x

end SmallPresentationStatements.RelationExtension

namespace SmallPresentationStatements.Homology

variable {X : Type} (N : Subgroup (FreeGroup X)) [N.Normal]

/-- The Hopf kernel includes canonically in the central relation group. -/
def hopfInclusion : PresentationKernel N →* RelationExtension.Kernel N where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hopfInclusion_injective : Function.Injective (hopfInclusion N) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : RelationExtension.Kernel N ↦ z.val) h

/-- The canonical Hopf exact sequence at the central relation group. -/
theorem hopf_exact : (RelationExtension.boundary N).ker = (hopfInclusion N).range := by
  apply le_antisymm
  · intro x hx
    have hderived : x.val ∈ commutator (RelationExtension.Total N) := by
      rw [← RelationExtension.abelianProjection_ker N]
      exact hx
    exact ⟨⟨⟨x.val, hderived⟩, x.property⟩, rfl⟩
  · rintro _ ⟨x, rfl⟩
    change x.val.val ∈ (RelationExtension.abelianProjection N).ker
    rw [RelationExtension.abelianProjection_ker]
    exact x.val.property

/-- All exactness and endpoint properties of the integral Hopf presentation sequence. -/
theorem presentation_exact_sequence :
    Function.Injective (hopfInclusion N) ∧
    (RelationExtension.boundary N).ker = (hopfInclusion N).range ∧
    (RelationExtension.abelianQuotient N).ker = (RelationExtension.boundary N).range ∧
    Function.Surjective (RelationExtension.abelianQuotient N) :=
  ⟨hopfInclusion_injective N, hopf_exact N, RelationExtension.abelianQuotient_ker N,
    RelationExtension.abelianQuotient_surjective N⟩

end SmallPresentationStatements.Homology
