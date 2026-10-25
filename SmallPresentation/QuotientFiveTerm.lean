module

public import SmallPresentation.HopfExact

/-!
# The five-term quotient sequence in Hopf coordinates

Given any free presentation `p : FreeGroup X →* B` and any normal subgroup `N`
of `B`, this module proves the exact sequence from the Hopf kernel of `B` to
the Hopf kernel of `B/N`, then to `N/[N,B]`, `B`'s abelianization, and finally
the abelianization of `B/N`. Every map is specified. No geometric hypothesis
or homology theorem is assumed.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology.QuotientSequence

open scoped commutatorElement

variable {X B : Type} [Group B] (p : FreeGroup X →* B)
    (N : Subgroup B) [N.Normal]

abbrev relations := N.comap p

omit [N.Normal] in
theorem originalRelations_le : p.ker ≤ relations p N := by
  intro x hx
  change p x ∈ N
  rw [show p x = 1 from hx]
  exact N.one_mem

/-- The quotient-induced map between the two Hopf presentation kernels. -/
def baseMap : PresentationKernel p.ker →* PresentationKernel (relations p N) :=
  presentationMap p.ker (relations p N) (MonoidHom.id _) (originalRelations_le p N)

/-- Evaluation of free words in the central relation extension of the base group. -/
def total : RelationExtension.Total (relations p N) →* RelationExtension.Total N :=
  QuotientGroup.map _ _ p (by
    apply Subgroup.commutator_le.mpr
    intro n hn x _
    change p ⁅n,x⁆ ∈ RelationExtension.commutatorKernel N
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hn (Subgroup.mem_top _))

theorem total_projects (x : RelationExtension.Total (relations p N)) :
    RelationExtension.projection N (total p N x) =
      QuotientGroup.map (relations p N) N p le_rfl
        (RelationExtension.projection (relations p N) x) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

/-- The transgression sends a lifted relation to its class modulo `[N,B]`. -/
def transgression : PresentationKernel (relations p N) →* RelationExtension.Kernel N :=
  ((total p N).comp ((commutator (RelationExtension.Total (relations p N))).subtype.comp
    (PresentationKernel (relations p N)).subtype)).codRestrict _ (by
      intro x
      change RelationExtension.projection N (total p N x.val.val) = 1
      rw [total_projects, show RelationExtension.projection (relations p N) x.val.val = 1
        from x.property, map_one])

omit [N.Normal] in
theorem image_commutator_relations (hp : Function.Surjective p) :
    (RelationExtension.commutatorKernel (relations p N)).map p =
      RelationExtension.commutatorKernel N := by
  rw [RelationExtension.commutatorKernel, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective hp, Subgroup.map_top_of_surjective p hp]

theorem transgression_baseMap (x : PresentationKernel p.ker) :
    transgression p N (baseMap p N x) = 1 := by
  apply Subtype.ext
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (RelationExtension.commutatorKernel p.ker) x.val.val
  have hp : p y = 1 := by
    have h : QuotientGroup.mk' p.ker y = 1 := by
      rw [← RelationExtension.projection_mk, hy]
      exact x.property
    exact (QuotientGroup.eq_one_iff y).mp h
  change total p N (totalMap p.ker (relations p N) (MonoidHom.id _)
    (originalRelations_le p N) x.val.val) = 1
  rw [← hy]
  change QuotientGroup.mk' (RelationExtension.commutatorKernel N) (p y) = 1
  rw [hp, map_one]

/-- Exactness at the quotient's Hopf kernel. -/
theorem transgression_ker (hp : Function.Surjective p) :
    (transgression p N).ker = (baseMap p N).range := by
  apply le_antisymm
  · intro x hx
    have hxderived : x.val.val ∈ commutator (RelationExtension.Total (relations p N)) :=
      x.val.property
    rw [← map_commutator_of_surjective
      (QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel (relations p N)))]
      at hxderived
    obtain ⟨y, hyderived, hy⟩ := hxderived
    have hpy : p y ∈ RelationExtension.commutatorKernel N := by
      apply (QuotientGroup.eq_one_iff (p y)).mp
      have hh := congrArg Subtype.val hx
      change total p N x.val.val = 1 at hh
      rw [← hy] at hh
      exact hh
    rw [← image_commutator_relations p N hp] at hpy
    obtain ⟨z, hz, hpz⟩ := hpy
    have hzderived : z ∈ commutator (FreeGroup X) :=
      (Subgroup.commutator_mono le_top le_rfl) hz
    have hyr : y * z⁻¹ ∈ p.ker := by
      change p (y * z⁻¹) = 1
      rw [map_mul, map_inv, hpz, mul_inv_cancel]
    have hyd : QuotientGroup.mk' (RelationExtension.commutatorKernel p.ker) (y * z⁻¹) ∈
        commutator (RelationExtension.Total p.ker) := by
      rw [← map_commutator_of_surjective
        (QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel p.ker))]
      exact ⟨y * z⁻¹, (commutator (FreeGroup X)).mul_mem hyderived
        ((commutator (FreeGroup X)).inv_mem hzderived), rfl⟩
    let a : PresentationKernel p.ker :=
      ⟨⟨QuotientGroup.mk' (RelationExtension.commutatorKernel p.ker) (y * z⁻¹), hyd⟩,
        (QuotientGroup.eq_one_iff _).mpr hyr⟩
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change QuotientGroup.mk' (RelationExtension.commutatorKernel (relations p N))
      (y * z⁻¹) = x.val.val
    have hz' : QuotientGroup.mk' (RelationExtension.commutatorKernel (relations p N)) z = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hz
    rw [map_mul, map_inv, hz', inv_one, mul_one]
    exact hy
  · rintro _ ⟨x, rfl⟩
    exact transgression_baseMap p N x

/-- Exactness at the central relation coinvariants. -/
theorem boundary_ker (hp : Function.Surjective p) :
    (RelationExtension.boundary N).ker = (transgression p N).range := by
  apply le_antisymm
  · intro x hx
    have hxderived : x.val ∈ commutator (RelationExtension.Total N) := by
      rw [← RelationExtension.abelianProjection_ker N]
      exact hx
    rw [← map_commutator_of_surjective
      (QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel N))] at hxderived
    obtain ⟨y, hyderived, hy⟩ := hxderived
    rw [← map_commutator_of_surjective hp] at hyderived
    obtain ⟨z, hzderived, hz⟩ := hyderived
    have hzn : z ∈ relations p N := by
      change p z ∈ N
      rw [hz]
      apply (QuotientGroup.eq_one_iff y).mp
      change QuotientGroup.mk' N y = 1
      rw [← RelationExtension.projection_mk, hy]
      exact x.property
    have hzd : QuotientGroup.mk' (RelationExtension.commutatorKernel (relations p N)) z ∈
        commutator (RelationExtension.Total (relations p N)) := by
      rw [← map_commutator_of_surjective
        (QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel (relations p N)))]
      exact ⟨z, hzderived, rfl⟩
    refine ⟨⟨⟨QuotientGroup.mk' (RelationExtension.commutatorKernel (relations p N)) z,
      hzd⟩, (QuotientGroup.eq_one_iff z).mpr hzn⟩, ?_⟩
    apply Subtype.ext
    change QuotientGroup.mk' (RelationExtension.commutatorKernel N) (p z) = x.val
    rw [hz, hy]
  · rintro _ ⟨x, rfl⟩
    change total p N x.val.val ∈ (RelationExtension.abelianProjection N).ker
    rw [RelationExtension.abelianProjection_ker]
    have hmap : (commutator (RelationExtension.Total (relations p N))).map (total p N) ≤
        commutator (RelationExtension.Total N) := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap ⟨x.val.val, x.val.property, rfl⟩

/-- The five-term quotient sequence, expressed in arbitrary free-presentation coordinates. -/
theorem exact_sequence (hp : Function.Surjective p) :
    (transgression p N).ker = (baseMap p N).range ∧
    (RelationExtension.boundary N).ker = (transgression p N).range ∧
    (RelationExtension.abelianQuotient N).ker = (RelationExtension.boundary N).range ∧
    Function.Surjective (RelationExtension.abelianQuotient N) :=
  ⟨transgression_ker p N hp, boundary_ker p N hp,
    RelationExtension.abelianQuotient_ker N, RelationExtension.abelianQuotient_surjective N⟩

end SmallPresentationStatements.Homology.QuotientSequence
