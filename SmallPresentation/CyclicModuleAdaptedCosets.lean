module

public import SmallPresentation.CyclicModuleGroupOrbit
public import SmallPresentation.RelationDerivativeCosets
public import Mathlib.GroupTheory.DoubleCoset

/-! Cyclically adapted coset representatives. A finite subgroup and a torsion-free
subgroup have trivial intersection with every conjugate. Consequently each double
coset has unique coordinates from these two subgroups. For a cyclic subgroup,
inverse-power coordinates give representatives on which translation is pure rotation. -/
@[expose] public section

namespace SmallPresentationStatements.CyclicModule

variable {Q : Type*} [Group Q]

/-- Assemble double-coset representatives with the left and right subgroup coordinates. -/
noncomputable def doubleCosetAssembly (C H : Subgroup Q)
    (x : DoubleCoset.Quotient (C : Set Q) H × C × H) : Q :=
  (x.2.1 : Q) * x.1.out * (x.2.2 : Q)

theorem doubleCosetAssembly_bijective (C H : Subgroup Q)
    [Finite C] [IsMulTorsionFree H] : Function.Bijective (doubleCosetAssembly C H) := by
  constructor
  · rintro ⟨b, c, h⟩ ⟨d, e, k⟩ he
    have hclass (b : DoubleCoset.Quotient (C : Set Q) H) (c : C) (h : H) :
        DoubleCoset.mk C H ((c : Q) * b.out * (h : Q)) = b := by
      calc
        _ = DoubleCoset.mk C H b.out := by
          apply (DoubleCoset.eq).mpr
          exact ⟨(c : Q)⁻¹, C.inv_mem c.property, (h : Q)⁻¹, H.inv_mem h.property,
            by simp [mul_assoc]⟩
        _ = b := Quotient.out_eq' b
    have hb : b = d := by
      have hh := congrArg (DoubleCoset.mk C H) he
      simpa only [doubleCosetAssembly, hclass] using hh
    subst d
    have hce : c = e := by
      apply finite_subgroup_coset_injective H C b.out
      have hh := congrArg (fun q : Q ↦ (QuotientGroup.mk q : Q ⧸ H)) he
      simpa only [doubleCosetAssembly, QuotientGroup.mk_mul_of_mem _ h.property,
        QuotientGroup.mk_mul_of_mem _ k.property] using hh
    subst e
    have hhk : h = k := Subtype.ext (mul_left_cancel he)
    subst k
    rfl
  · intro q
    let b := DoubleCoset.mk C H q
    have hr : DoubleCoset.mk C H b.out = DoubleCoset.mk C H q := Quotient.out_eq' b
    obtain ⟨c, hc, h, hh, he⟩ := DoubleCoset.eq.mp hr
    exact ⟨(b, ⟨c, hc⟩, ⟨h, hh⟩), he.symm⟩

/-- Inverse powers give a rotation-compatible choice in each cyclic orbit of factor cosets. -/
noncomputable def adaptedRepresentative (H : Subgroup Q) (c : Q)
    (n : ℕ) (b : DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) H × Fin (n + 1)) : Q :=
  (c ^ b.2.val)⁻¹ * b.1.out

theorem adaptedRepresentative_step (H : Subgroup Q) (c : Q) (n : ℕ)
    (hn : orderOf c = n + 1)
    (b : DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) H) (j : Fin (n + 1)) :
    c * adaptedRepresentative H c n (b, finRotate (n + 1) j) =
      adaptedRepresentative H c n (b, j) := by
  change c * ((c ^ (finRotate (n + 1) j).val)⁻¹ * b.out) = (c ^ j.val)⁻¹ * b.out
  by_cases hj : j.val < n
  · have hr : (finRotate (n + 1) j).val = j.val + 1 :=
      congrArg Fin.val (finRotate_of_lt hj)
    rw [hr, pow_succ, mul_inv_rev]
    simp [mul_assoc]
  · have hjlast : j = Fin.last n := by apply Fin.ext; change j.val = n; omega
    subst j
    rw [finRotate_last]
    simp only [Fin.val_zero, pow_zero, inv_one, one_mul, Fin.val_last]
    have hp : c * c ^ n = 1 := by rw [← pow_succ', ← hn, pow_orderOf_eq_one]
    exact congrArg (fun x : Q ↦ x * b.out) ((eq_inv_iff_mul_eq_one).mpr hp)

/-- Double-coset coordinates reorganized as a coset label and a factor element. -/
noncomputable def adaptedIndexEquiv (H : Subgroup Q) (c : Q) (hc : IsOfFinOrder c)
    (n : ℕ) (hn : orderOf c = n + 1) :
    ((DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) H × Fin (n + 1)) × H) ≃
      DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) H × Subgroup.zpowers c × H :=
  (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
    (Equiv.prodCongr ((cyclicPowerIndex c hc n hn).trans (Equiv.inv _)) (Equiv.refl _)))

theorem adaptedRepresentative_bijective (H : Subgroup Q) [IsMulTorsionFree H]
    (c : Q) (hc : IsOfFinOrder c) (n : ℕ) (hn : orderOf c = n + 1) :
    Function.Bijective (fun x :
      (DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) H × Fin (n + 1)) × H ↦
        adaptedRepresentative H c n x.1 * (x.2 : Q)) := by
  let : Finite (Subgroup.zpowers c) := Finite.of_equiv (Fin (n + 1))
    (cyclicPowerIndex c hc n hn)
  exact (doubleCosetAssembly_bijective (Subgroup.zpowers c) H).comp
    (adaptedIndexEquiv H c hc n hn).bijective

section Homomorphism

variable {G : Type} {Q : Type} [Group G] [Group Q]

/-- Cyclically adapted representatives for any injectively embedded torsion-free factor. -/
noncomputable def adaptedCosetData (φ : G →* Q) (hφ : Function.Injective φ)
    [IsMulTorsionFree G] (c : Q) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1) : RelationDerivative.CosetData φ := by
  letI : IsMulTorsionFree φ.range := Function.Injective.isMulTorsionFree
    (MonoidHom.ofInjective hφ).symm.toMonoidHom (MonoidHom.ofInjective hφ).symm.injective
  refine ⟨DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) φ.range × Fin (n + 1),
    adaptedRepresentative φ.range c n, ?_⟩
  exact (adaptedRepresentative_bijective φ.range c hc n hn).comp
    (Equiv.prodCongr (Equiv.refl _) (MonoidHom.ofInjective hφ).toEquiv).bijective

/-- The chosen representatives rotate exactly, without a correcting factor element. -/
theorem adaptedCosetData_step (φ : G →* Q) (hφ : Function.Injective φ)
    [IsMulTorsionFree G] (c : Q) (hc : IsOfFinOrder c) (n : ℕ)
    (hn : orderOf c = n + 1)
    (b : DoubleCoset.Quotient (Subgroup.zpowers c : Set Q) φ.range) (j : Fin (n + 1)) :
    c * (adaptedCosetData φ hφ c hc n hn).representative (b, finRotate (n + 1) j) =
      (adaptedCosetData φ hφ c hc n hn).representative (b, j) :=
  adaptedRepresentative_step φ.range c n hn b j

end Homomorphism

end SmallPresentationStatements.CyclicModule
