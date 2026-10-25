module

public import SmallPresentation.CyclicModulePermutation
public import SmallPresentation.CyclicModuleCosets

/-! Explicit cyclic orbit coordinates for left translation on a group. -/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

variable {G : Type*} [Group G]

/-- Left translation, as a permutation of the underlying set. -/
def leftTranslation (c : G) : Equiv.Perm G where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by simp
  right_inv x := by simp

/-- Assemble inverse coset coordinates into a group element. -/
noncomputable def inverseCosetAssembly (H : Subgroup G) (x : (G ⧸ H) × H) : G :=
  (x.2 : G)⁻¹ * x.1.out⁻¹

theorem inverseCosetAssembly_bijective (H : Subgroup G) :
    Function.Bijective (inverseCosetAssembly H) := by
  constructor
  · rintro ⟨q, h⟩ ⟨r, k⟩ he
    have he' : q.out * (h : G) = r.out * (k : G) := by
      simpa only [inverseCosetAssembly, mul_inv_rev, inv_inv] using congrArg Inv.inv he
    have hq : q = r := by
      have hm := congrArg (fun g : G ↦ (QuotientGroup.mk g : G ⧸ H)) he'
      simpa only [QuotientGroup.mk_mul_of_mem _ h.property,
        QuotientGroup.mk_mul_of_mem _ k.property, Quotient.out_eq'] using hm
    subst r
    have hk : h = k := Subtype.ext (mul_left_cancel he')
    subst k
    rfl
  · intro g
    let q : G ⧸ H := QuotientGroup.mk g⁻¹
    have hm : q.out⁻¹ * g⁻¹ ∈ H := QuotientGroup.eq.mp (Quotient.out_eq' q)
    refine ⟨(q, ⟨q.out⁻¹ * g⁻¹, hm⟩), ?_⟩
    simp [inverseCosetAssembly, mul_assoc]

/-- Inversion turns the usual left-coset decomposition into coordinates for left translation. -/
noncomputable def inverseCosetCoordinates (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  (Equiv.ofBijective (inverseCosetAssembly H) (inverseCosetAssembly_bijective H)).symm

theorem inverseCosetCoordinates_symm (H : Subgroup G) (q : G ⧸ H) (h : H) :
    (inverseCosetCoordinates H).symm (q, h) = (h : G)⁻¹ * q.out⁻¹ := rfl

/-- Index the finite cyclic subgroup by powers with the required tuple length. -/
noncomputable def cyclicPowerIndex (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) : Fin (n + 1) ≃ Subgroup.zpowers c :=
  (finCongr hn.symm).trans (finEquivZPowers hc)

theorem cyclicPowerIndex_apply (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) (j : Fin (n + 1)) :
    (cyclicPowerIndex c hc n hn j : G) = c ^ j.val := rfl

/-- Each right coset is a cyclic orbit; the coordinates use inverse powers. -/
noncomputable def groupOrbitCoordinates (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) : G ≃ (G ⧸ Subgroup.zpowers c) × Fin (n + 1) :=
  (inverseCosetCoordinates (Subgroup.zpowers c)).trans
    (Equiv.prodCongr (Equiv.refl _) (cyclicPowerIndex c hc n hn).symm)

theorem groupOrbitCoordinates_symm (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) (q : G ⧸ Subgroup.zpowers c) (j : Fin (n + 1)) :
    (groupOrbitCoordinates c hc n hn).symm (q, j) = (c ^ j.val)⁻¹ * q.out⁻¹ := by
  simp [groupOrbitCoordinates, inverseCosetCoordinates_symm, cyclicPowerIndex_apply]

theorem groupOrbitCoordinates_step (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) (q : G ⧸ Subgroup.zpowers c) (j : Fin (n + 1)) :
    leftTranslation c ((groupOrbitCoordinates c hc n hn).symm
      (q, finRotate (n + 1) j)) = (groupOrbitCoordinates c hc n hn).symm (q, j) := by
  simp only [groupOrbitCoordinates_symm]
  change c * ((c ^ (finRotate (n + 1) j).val)⁻¹ * q.out⁻¹) =
    (c ^ j.val)⁻¹ * q.out⁻¹
  by_cases hj : j.val < n
  · have hr : (finRotate (n + 1) j).val = j.val + 1 :=
      congrArg Fin.val (finRotate_of_lt hj)
    rw [hr, pow_succ, mul_inv_rev]
    simp [mul_assoc]
  · have hjlast : j = Fin.last n := by
      apply Fin.ext
      change j.val = n
      omega
    subst j
    rw [finRotate_last]
    simp only [Fin.val_zero, pow_zero, inv_one, one_mul, Fin.val_last]
    have hp : c * c ^ n = 1 := by rw [← pow_succ', ← hn, pow_orderOf_eq_one]
    have hc' : c = (c ^ n)⁻¹ := (eq_inv_iff_mul_eq_one).mpr hp
    exact congrArg (fun x : G ↦ x * q.out⁻¹) hc'

/-- Left translation of the first coordinate of a labelled group element. -/
def labelledTranslation (X : Type*) (c : G) : Equiv.Perm (G × X) :=
  Equiv.prodCongr (leftTranslation c) (Equiv.refl X)

/-- Retain an arbitrary label while grouping the group coordinate into cyclic orbits. -/
noncomputable def labelledOrbitCoordinates (X : Type*) (c : G) (hc : IsOfFinOrder c)
    (n : ℕ) (hn : orderOf c = n + 1) :
    G × X ≃ ((G ⧸ Subgroup.zpowers c) × X) × Fin (n + 1) where
  toFun x := (((groupOrbitCoordinates c hc n hn x.1).1, x.2),
    (groupOrbitCoordinates c hc n hn x.1).2)
  invFun y := ((groupOrbitCoordinates c hc n hn).symm (y.1.1, y.2), y.1.2)
  left_inv x := by simp
  right_inv y := by simp

theorem labelledOrbitCoordinates_step (X : Type*) (c : G) (hc : IsOfFinOrder c)
    (n : ℕ) (hn : orderOf c = n + 1)
    (q : (G ⧸ Subgroup.zpowers c) × X) (j : Fin (n + 1)) :
    labelledTranslation X c ((labelledOrbitCoordinates X c hc n hn).symm
      (q, finRotate (n + 1) j)) = (labelledOrbitCoordinates X c hc n hn).symm (q, j) := by
  apply Prod.ext
  · exact groupOrbitCoordinates_step c hc n hn q.1 j
  · rfl

/-- The actual finite-order left-translation action on vertex chains is exact in both parities. -/
theorem group_translation_exact (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) :
    let h := permutation_pow_order n (groupOrbitCoordinates c hc n hn)
      (leftTranslation c) (groupOrbitCoordinates_step c hc n hn)
    (ofFiniteOrder (permutationAction (leftTranslation c)) (n + 1) h).EvenExact ∧
      (ofFiniteOrder (permutationAction (leftTranslation c)) (n + 1) h).OddExact :=
  permutation_exact n (groupOrbitCoordinates c hc n hn)
    (leftTranslation c) (groupOrbitCoordinates_step c hc n hn)

/-- The same exactness holds for labelled edge chains, with an arbitrary label set. -/
theorem labelled_translation_exact (X : Type*) (c : G) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) :
    let h := permutation_pow_order n (labelledOrbitCoordinates X c hc n hn)
      (labelledTranslation X c) (labelledOrbitCoordinates_step X c hc n hn)
    (ofFiniteOrder (permutationAction (labelledTranslation X c)) (n + 1) h).EvenExact ∧
      (ofFiniteOrder (permutationAction (labelledTranslation X c)) (n + 1) h).OddExact :=
  permutation_exact n (labelledOrbitCoordinates X c hc n hn)
    (labelledTranslation X c) (labelledOrbitCoordinates_step X c hc n hn)

end SmallPresentationStatements.CyclicModule
