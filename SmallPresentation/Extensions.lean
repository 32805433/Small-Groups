module

public import SmallPresentation.Basic

/-! # Torsion-free kernels and quotients -/
public section

namespace SmallPresentationStatements

/-- No surjectivity is needed: a torsion-free kernel and target suffice. -/
theorem torsionfree_of_kernel {E G : Type*} [Group E] [Group G]
    (π : E →* G) [IsMulTorsionFree π.ker] [IsMulTorsionFree G] :
    IsMulTorsionFree E := by
  constructor
  intro n hn a b hab hp
  have hcomm : Commute (π a) (π b) := by
    simpa only [Commute, SemiconjBy, map_mul] using congrArg π hab
  have hπ : π a = π b := hcomm.eq_of_pow_eq_pow hn (by
    simpa only [map_pow] using congrArg π hp)
  let z : π.ker := ⟨a * b⁻¹, by simp [MonoidHom.mem_ker, hπ]⟩
  have hzpow : z ^ n = 1 := by
    apply Subtype.ext
    change (a * b⁻¹) ^ n = 1
    rw [(hab.inv_right).mul_pow, inv_pow, hp, mul_inv_cancel]
  have hz : z = 1 := (pow_eq_one_iff_left hn).mp hzpow
  exact eq_of_mul_inv_eq_one (congrArg Subtype.val hz)

end SmallPresentationStatements
