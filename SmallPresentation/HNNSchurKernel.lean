module

public import SmallPresentation.SchurKernelQuotient
public import SmallPresentation.HNNCentralTwo
public import SmallPresentation.CentralExtensionComparison

/-!
# The degree-two HNN kernel formula for projective edge abelianizations

The proof constructs a central extension of the vertex group retaining precisely
the quotient of its Schur multiplier by the edge differences. Equal edge Hopf
obstructions identify the pullback extensions. HNN normal forms preserve the
vertex extension, and central lifting detects that no further Schur classes die.
No Mayer--Vietoris theorem is assumed.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable {G A B : Type} [Group G] [Group A] [Group B]
variable (l₁ r₁ : A →* G) (l₂ r₂ : B →* G)
variable (hl₁ : Function.Injective l₁) (hr₁ : Function.Injective r₁)
    (hl₂ : Function.Injective l₂) (hr₂ : Function.Injective r₂)

/-- The actual degree-two edge image is the full kernel of the actual vertex map,
provided the two edge abelianizations are projective over the integers. -/
theorem twoHNN_schur_ker [Module.Projective ℤ (H₁ A)] [Module.Projective ℤ (H₁ B)] :
    (map₂ (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂)).ker =
      (edge₂ G A B l₁ r₁ l₂ r₂).range := by
  let S : Subgroup (Schur G) := (edge₂ G A B l₁ r₁ l₂ r₂).range.toSubgroup
  let π := SchurKernelQuotient.projection S
  let q₀ := SchurKernelQuotient.quotient S
  have hπ := SchurKernelQuotient.projection_surjective S
  have hc := SchurKernelQuotient.projection_central S
  have hleft : ∀ x : Schur A, schurMap l₁ x * (schurMap r₁ x)⁻¹ ∈ S := by
    intro x
    refine ⟨(Additive.ofMul x, 0), ?_⟩
    change edge₂ G A B l₁ r₁ l₂ r₂ (Additive.ofMul x, 0) =
      Additive.ofMul (schurMap l₁ x * (schurMap r₁ x)⁻¹)
    simp only [edge₂, AddMonoidHom.coprod_apply, AddMonoidHom.sub_apply,
      map_zero, add_zero]
    change Additive.ofMul (schurMap l₁ x / schurMap r₁ x) = _
    rw [div_eq_mul_inv]
  have hright : ∀ x : Schur B, schurMap l₂ x * (schurMap r₂ x)⁻¹ ∈ S := by
    intro x
    refine ⟨(0, Additive.ofMul x), ?_⟩
    change edge₂ G A B l₁ r₁ l₂ r₂ (0, Additive.ofMul x) =
      Additive.ofMul (schurMap l₂ x * (schurMap r₂ x)⁻¹)
    simp only [edge₂, AddMonoidHom.coprod_apply, AddMonoidHom.sub_apply,
      map_zero, zero_add]
    change Additive.ofMul (schurMap l₂ x / schurMap r₂ x) = _
    rw [div_eq_mul_inv]
  have lift_projects {J : Type} [Group J] (f : J →* G) :
      π.comp (q₀.comp (canonicalTotalMap f)) = f.comp (totalEvaluation J) := by
    apply MonoidHom.ext
    intro x
    exact canonicalTotalMap_projection f x
  obtain ⟨e₁⟩ := pullbackOverEquiv_of_hopf_eq π hc l₁ r₁
    (q₀.comp (canonicalTotalMap l₁)) (q₀.comp (canonicalTotalMap r₁))
    (lift_projects l₁) (lift_projects r₁)
    (SchurKernelQuotient.equal_obstruction S l₁ r₁ hleft)
  obtain ⟨e₂⟩ := pullbackOverEquiv_of_hopf_eq π hc l₂ r₂
    (q₀.comp (canonicalTotalMap l₂)) (q₀.comp (canonicalTotalMap r₂))
    (lift_projects l₂) (lift_projects r₂)
    (SchurKernelQuotient.equal_obstruction S l₂ r₂ hright)
  obtain ⟨L, instL, q, j, hq, hqc, hj, hqj⟩ :=
    twoHNN_central_extension l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂ π hπ hc e₁ e₂
  let base := twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  have hσ : q.comp (j.comp q₀) = base.comp (totalEvaluation G) := by
    rw [← MonoidHom.comp_assoc, hqj, MonoidHom.comp_assoc]
    rfl
  have hdetect := schurMap_ker_le_centralLift_ker base q hq hqc (j.comp q₀) hσ
  apply le_antisymm
  · intro x hx
    have hz : j (q₀ (schurInclusion G x.toMul)) = 1 := hdetect hx
    have hz' : q₀ (schurInclusion G x.toMul) = 1 := hj (by simpa using hz)
    have hS : x.toMul ∈ ((SchurKernelQuotient.quotient S).comp (schurInclusion G)).ker := hz'
    rw [SchurKernelQuotient.schur_ker] at hS
    exact hS
  · rintro _ ⟨x, rfl⟩
    let P := twoHNNPresentation G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
    let e := boolDirectSumEquiv (fun b ↦ H₂ (twoEdgeGroups A B b))
    have h := DFunLike.congr_fun P.map₂_base_boundary₂ (e.symm x)
    rw [two_boundary₂] at h
    change map₂ P.base (edge₂ G A B l₁ r₁ l₂ r₂ (e (e.symm x))) = 0 at h
    rw [AddEquiv.apply_symm_apply] at h
    exact h

end SmallPresentationStatements.Homology
