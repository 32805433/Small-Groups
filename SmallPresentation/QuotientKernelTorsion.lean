module

public import Mathlib.GroupTheory.OrderOfElement

/-! Torsion passes through a quotient of the kernel of an arbitrary homomorphism. -/
@[expose] public section

namespace SmallPresentationStatements

variable {C B : Type*} [Group C] [Group B]

/-- If the image group and the remaining kernel quotient are torsion-free,
so is the total quotient. Surjectivity and centrality are unnecessary. -/
theorem quotient_torsionFree_of_kernelQuotient (π : C →* B)
    (M : Subgroup C) [M.Normal] (hM : M ≤ π.ker)
    (hB : IsMulTorsionFree B)
    (hA : IsMulTorsionFree (π.ker ⧸ M.comap π.ker.subtype)) :
    IsMulTorsionFree (C ⧸ M) := by
  let := hB
  let := hA
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro x hx hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective M x
  have hcn : c ^ n ∈ M := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' M (c ^ n) = 1
    simpa only [map_pow] using hpow
  have hπ : π c = 1 := by
    apply (pow_eq_one_iff_left hn.ne').mp
    change π c ^ n = 1
    rw [← map_pow]
    exact hM hcn
  let a : π.ker := ⟨c, hπ⟩
  have han : a ^ n ∈ M.comap π.ker.subtype := hcn
  have ha : QuotientGroup.mk' (M.comap π.ker.subtype) a = 1 := by
    apply (pow_eq_one_iff_left hn.ne').mp
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr han
  have ham : a ∈ M.comap π.ker.subtype := (QuotientGroup.eq_one_iff _).mp ha
  apply hx
  exact (QuotientGroup.eq_one_iff c).mpr ham

end SmallPresentationStatements
