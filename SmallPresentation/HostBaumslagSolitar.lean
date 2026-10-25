module

public import SmallPresentation.HNNTorsion
public import SmallPresentation.UniversalGroup.Foundations.HNN.Identifying

/-! The Baumslag–Solitar group `t^s = t²`, constructed as an actual ascending
HNN extension of the infinite cyclic group, with its universal property and torsion theorem. -/
@[expose] public section

namespace SmallPresentationStatements.HostBS

def twice : Multiplicative ℤ →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (2 * z.toAdd)
  map_one' := rfl
  map_mul' x y := by simp [Int.mul_add]

theorem twice_injective : Function.Injective twice := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  change 2 * x.toAdd = 2 * y.toAdd at h'
  omega

noncomputable abbrev Group := UniversalGroup.IdentifyingHNN (MonoidHom.id (Multiplicative ℤ))
  twice Function.injective_id twice_injective

noncomputable def of : Multiplicative ℤ →* Group := UniversalGroup.IdentifyingHNN.of _ _ _ _
noncomputable def t : Group := of (Multiplicative.ofAdd 1)
noncomputable def s : Group := UniversalGroup.IdentifyingHNN.stable _ _ _ _

theorem of_zpow (z : Multiplicative ℤ) : of z = t ^ z.toAdd := by
  rw [t, ← map_zpow]
  congr 1
  apply Multiplicative.toAdd.injective
  simp

theorem relation : s⁻¹ * t * s = t ^ 2 := by
  have h := UniversalGroup.IdentifyingHNN.conjugates
    (MonoidHom.id (Multiplicative ℤ)) twice Function.injective_id twice_injective
    (Multiplicative.ofAdd 1)
  change s⁻¹ * t * s = of (twice (Multiplicative.ofAdd 1)) at h
  rw [h, of_zpow]
  rfl

theorem torsionFree : IsMulTorsionFree Group :=
  HNNTorsion.torsionFree (UniversalGroup.rangeEquiv _ _ Function.injective_id twice_injective)

theorem generated_by (K : Subgroup Group) (ht : t ∈ K) (hs : s ∈ K) (x : Group) : x ∈ K := by
  induction x using HNNExtension.induction_on with
  | of z =>
    change of z ∈ K
    rw [of_zpow]
    exact K.zpow_mem ht _
  | t =>
    have h := K.inv_mem hs
    simpa only [s, UniversalGroup.IdentifyingHNN.stable, inv_inv] using h
  | mul x y hx hy => exact K.mul_mem hx hy
  | inv x hx => exact K.inv_mem hx

variable {H : Type*} [_root_.Group H] (a b : H) (h : b⁻¹ * a * b = a ^ 2)

def powers (a : H) : Multiplicative ℤ →* H where
  toFun z := a ^ z.toAdd
  map_one' := by simp
  map_mul' x y := by simp [zpow_add]

noncomputable def lift : Group →* H :=
  UniversalGroup.IdentifyingHNN.lift _ _ _ _ (powers a) b (by
    intro z
    change b⁻¹ * a ^ z.toAdd * b = a ^ (2 * z.toAdd)
    have hc := map_zpow (MulAut.conj b⁻¹) a z.toAdd
    simp only [MulAut.conj_apply, inv_inv] at hc
    rw [hc, h]
    rw [← zpow_natCast, ← zpow_mul]
    rfl)

@[simp] theorem lift_t : lift a b h t = a := by
  change lift a b h (of (Multiplicative.ofAdd 1)) = a
  simp [lift, of, powers]

@[simp] theorem lift_s : lift a b h s = b :=
  UniversalGroup.IdentifyingHNN.lift_stable _ _ _ _ _ _ _

theorem hom_ext {f g : Group →* H} (ht : f t = g t) (hs : f s = g s) : f = g := by
  apply UniversalGroup.IdentifyingHNN.hom_ext
  · intro z
    change f (of z) = g (of z)
    rw [of_zpow, map_zpow, map_zpow, ht]
  · exact hs

end SmallPresentationStatements.HostBS
