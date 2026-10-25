module

public import SmallPresentation.FreeGroupCentralizer

/-! Root-free elements and conjugator bookkeeping. Equal conjugates of a root-free
relator in a free group have conjugators differing by a power of that relator, so
any quotient which kills the relator assigns those conjugators the same weight. -/
@[expose] public section

namespace SmallPresentationStatements.FreeGroupCentralizer

variable {G Q : Type*} [Group G] [Group Q]

/-- A root-free element is nonidentity and has no proper positive-power expression. -/
def RootFree (r : G) : Prop := ∀ (x : G) (n : ℕ), x ^ n = r → n = 1

theorem RootFree.ne_one {r : G} (hr : RootFree r) : r ≠ 1 := by
  intro h
  have he := hr 1 0 (by simp [h])
  omega

/-- Root-freeness of an image suffices for root-freeness before applying a homomorphism. -/
theorem RootFree.of_image (p : G →* Q) {r : G} (hr : RootFree (p r)) : RootFree r := by
  intro x n h
  apply hr (p x) n
  simpa only [map_pow] using congrArg p h

theorem RootFree.inv {r : G} (hr : RootFree r) : RootFree r⁻¹ := by
  intro x n h
  apply hr x⁻¹ n
  simpa only [inv_pow, inv_inv] using congrArg Inv.inv h

theorem RootFree.conjugate {r : G} (hr : RootFree r) (w : G) :
    RootFree (w * r * w⁻¹) := by
  intro x n h
  apply hr (w⁻¹ * x * w) n
  have he := congrArg (MulAut.conj w⁻¹) h
  simpa only [map_pow, MulAut.conj_apply, inv_inv, mul_assoc,
    inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using he

/-- An integral power representing a root-free element has exponent `1` or `-1`. -/
theorem RootFree.zpow_exponent {r z : G} (hr : RootFree r) {n : ℤ}
    (h : z ^ n = r) : n = 1 ∨ n = -1 := by
  cases n with
  | ofNat k =>
    have hk := hr z k (by simpa only [Int.ofNat_eq_natCast, zpow_natCast] using h)
    simp [hk]
  | negSucc k =>
    have hk := hr z⁻¹ (k + 1) (by simpa only [zpow_negSucc, inv_pow] using h)
    have hk0 : k = 0 := by omega
    simp [hk0]

variable [IsFreeGroup G]

/-- The centralizer of a root-free element is exactly its group of integral powers. -/
theorem mem_zpowers_of_commute_rootFree {r x : G} (hr : RootFree r) (hx : Commute x r) :
    x ∈ Subgroup.zpowers r := by
  obtain ⟨z, m, n, hm, hn⟩ := exists_common_zpow x r hx
  rcases hr.zpow_exponent hn with hn1 | hn1
  · have hz : z = r := by simpa only [hn1, zpow_one] using hn
    exact ⟨m, by simpa only [hz] using hm⟩
  · have hz : z⁻¹ = r := by simpa only [hn1, zpow_neg_one] using hn
    refine ⟨-m, ?_⟩
    change r ^ (-m) = x
    simpa only [← hz, inv_zpow, zpow_neg, inv_inv] using hm

/-- Root-free centralizers carry no elements beyond the indicated relator powers. -/
theorem centralizer_eq_zpowers {r : G} (hr : RootFree r) :
    Subgroup.centralizer ({r} : Set G) = Subgroup.zpowers r := by
  apply le_antisymm
  · intro x hx
    exact mem_zpowers_of_commute_rootFree hr
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
  · rintro x ⟨m, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.zpow_self r m).eq

/-- Equality of conjugates forces equality of conjugator images in every quotient
which kills a root-free relator. This is the weighted picture-label invariant. -/
theorem conjugator_image_eq (p : G →* Q) {r u v : G} (hr : RootFree r)
    (hkill : p r = 1) (h : u * r * u⁻¹ = v * r * v⁻¹) : p u = p v := by
  have hc : Commute (v⁻¹ * u) r := by
    change (v⁻¹ * u) * r = r * (v⁻¹ * u)
    have he := congrArg (fun t : G ↦ v⁻¹ * t * u) h
    simpa only [mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left,
      mul_inv_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using he
  obtain ⟨m, hm⟩ := mem_zpowers_of_commute_rootFree hr hc
  have hp : (p v)⁻¹ * p u = 1 := by
    have he := congrArg p hm
    simpa only [map_zpow, map_mul, map_inv, hkill, one_zpow] using he.symm
  exact (inv_mul_eq_one.mp hp).symm

end SmallPresentationStatements.FreeGroupCentralizer
