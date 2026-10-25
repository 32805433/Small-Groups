module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Free finite-subgroup actions on cosets of torsion-free subgroups

These are the group-theoretic hypotheses needed when an induced relation module
is restricted to a finite cyclic subgroup. The result holds for any finite subgroup.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

variable {G : Type*} [Group G]

/-- A finite-order element cannot have a nonidentity conjugate in a torsion-free subgroup. -/
theorem eq_one_of_conjugate_mem_torsionFree (H : Subgroup G) [IsMulTorsionFree H]
    {g : G} (hg : IsOfFinOrder g) (q : G) (hmem : q⁻¹ * g * q ∈ H) : g = 1 := by
  obtain ⟨n, hn, hpow⟩ := hg.exists_pow_eq_one
  let h : H := ⟨q⁻¹ * g * q, hmem⟩
  have hh : h ^ n = 1 := by
    apply Subtype.ext
    change (q⁻¹ * g * q) ^ n = 1
    simpa only [inv_inv, hpow, mul_one, inv_mul_cancel] using
      (conj_pow (a := q⁻¹) (b := g) (i := n))
  have he : h = 1 := (pow_eq_one_iff_left (Nat.ne_of_gt hn)).mp hh
  have he' : q⁻¹ * g * q = 1 := congrArg Subtype.val he
  have := congrArg (fun x : G ↦ q * x * q⁻¹) he'
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left,
    mul_inv_cancel_right, mul_one, one_mul] using this

/-- A finite subgroup acts freely on the cosets of a torsion-free subgroup. -/
theorem finite_subgroup_coset_injective (H C : Subgroup G)
    [IsMulTorsionFree H] [Finite C] (q : G) :
    Function.Injective (fun c : C ↦ (QuotientGroup.mk ((c : G) * q) : G ⧸ H)) := by
  intro c d hcd
  have hmem : q⁻¹ * ((c : G)⁻¹ * (d : G)) * q ∈ H := by
    have h := QuotientGroup.eq.mp hcd
    simpa only [mul_inv_rev, mul_assoc] using h
  have hfin : IsOfFinOrder ((c : G)⁻¹ * (d : G)) := by
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite (c⁻¹ * d)).exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    exact congrArg Subtype.val hp
  have he := eq_one_of_conjugate_mem_torsionFree H hfin q hmem
  apply Subtype.ext
  exact inv_mul_eq_one.mp he

end SmallPresentationStatements.CyclicModule
