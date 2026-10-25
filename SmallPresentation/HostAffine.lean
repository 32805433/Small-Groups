module

public import SmallPresentation.HostArithmetic

/-! # Affine transitivity on ordered pairs within one residue factor -/
@[expose] public section

namespace SmallPresentationStatements.HostAffine

def residue (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p)

/-- Every nonzero kernel element is `p` times a unit, integrally modulo `p²`. -/
theorem kernel_factor {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 2))
    (hx : x ≠ 0) (hr : residue p x = 0) :
    ∃ u : (ZMod (p ^ 2))ˣ, x = (p : ZMod (p ^ 2)) * (u : ZMod (p ^ 2)) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hd : p ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [residue, ZMod.castHom_apply, ZMod.cast_eq_val] using hr
  let k := x.val / p
  have hk : p * k = x.val := Nat.mul_div_cancel' hd
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    have hx0 : x.val = 0 := by rw [← hk, hk0, mul_zero]
    apply hx
    rw [← ZMod.natCast_zmod_val x, hx0, Nat.cast_zero]
  have hklt : k < p := by
    have hxlt := x.val_lt
    rw [← hk, pow_two] at hxlt
    exact (Nat.mul_lt_mul_left hp.pos).mp hxlt
  have hunit : IsUnit (k : ZMod (p ^ 2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)).mpr
      (Nat.not_dvd_of_pos_of_lt hkpos hklt)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← Nat.cast_mul, hk, ZMod.natCast_zmod_val]

/-- An invertible affine transformation carries any ordered pair of distinct
vertices in a residue factor to any other such pair. -/
theorem pair_transitive {p : ℕ} (hp : p.Prime)
    (i j u v : ZMod (p ^ 2)) (hij : i ≠ j) (huv : u ≠ v)
    (hrij : residue p i = residue p j) (hruv : residue p u = residue p v) :
    ∃ (a : (ZMod (p ^ 2))ˣ) (b : ZMod (p ^ 2)),
      (a : ZMod (p ^ 2)) * i + b = u ∧ (a : ZMod (p ^ 2)) * j + b = v := by
  obtain ⟨c, hc⟩ := kernel_factor hp (j - i) (sub_ne_zero.mpr hij.symm) (by
    rw [map_sub, hrij, sub_self])
  obtain ⟨d, hd⟩ := kernel_factor hp (v - u) (sub_ne_zero.mpr huv.symm) (by
    rw [map_sub, hruv, sub_self])
  let a := d * c⁻¹
  have hdiff : (a : ZMod (p ^ 2)) * (j - i) = v - u := by
    rw [hc, hd]
    have hcc : (↑(c⁻¹) : ZMod (p ^ 2)) * ↑c = 1 := by
      exact congrArg (fun z : (ZMod (p ^ 2))ˣ ↦ (z : ZMod (p ^ 2))) (inv_mul_cancel c)
    calc
      (a : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * ↑c) =
          (p : ZMod (p ^ 2)) * ↑d * ((↑(c⁻¹) : ZMod (p ^ 2)) * ↑c) := by
            simp only [a, Units.val_mul]
            ring
      _ = _ := by rw [hcc, mul_one]
  refine ⟨a, u - (a : ZMod (p ^ 2)) * i, by ring, ?_⟩
  calc
    (a : ZMod (p ^ 2)) * j + (u - (a : ZMod (p ^ 2)) * i) =
        (a : ZMod (p ^ 2)) * (j - i) + u := by ring
    _ = v := by rw [hdiff]; ring

theorem preserves_residue {p : ℕ} (a : (ZMod (p ^ 2))ˣ) (b i j : ZMod (p ^ 2)) :
    residue p ((a : ZMod (p ^ 2)) * i + b) =
      residue p ((a : ZMod (p ^ 2)) * j + b) ↔ residue p i = residue p j := by
  simp only [map_add, map_mul, add_left_inj]
  constructor
  · exact (Units.isUnit (Units.map (residue p).toMonoidHom a)).mul_left_cancel
  · intro h
    rw [h]

open HostAlgebra Elimination

variable {G : Type*} [Group G]

theorem translate_lamp (a t : G) (N : ℕ) [NeZero N]
    (hperiod : conjugate a (t ^ N) = a) (j : ZMod N) (k : ℕ) :
    cyclicLamp a t (j + (k : ZMod N)) = conjugate (cyclicLamp a t j) (t ^ k) := by
  induction k with
  | zero => simp [conjugate]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, cyclicLamp_shift a t N hperiod, ih]
    exact (conjugate_pow_right _ _ k).symm

theorem scale_lamp (a t s : G) (N : ℕ) [NeZero N]
    (ha : conjugate a s = a) (ht : conjugate t s = t ^ 2)
    (hperiod : conjugate a (t ^ N) = a) (j : ZMod N) (e : ℕ) :
    cyclicLamp a t ((2 : ZMod N) ^ e * j) =
      conjugate (cyclicLamp a t j) (s ^ e) := by
  induction e with
  | zero => simp [conjugate]
  | succ e ih =>
    rw [pow_succ', mul_assoc, cyclicLamp_double a t s N ha ht hperiod, ih]
    exact (conjugate_pow_right _ _ e).symm

/-- Every affine permutation used in the kernel argument is realized by an
actual word in the two stable letters, with its action checked on every lamp. -/
theorem affine_conjugator (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) {p : ℕ} (hp : p.Prime)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (hperiod : conjugate a (t ^ (p ^ 2)) = a)
    (u : (ZMod (p ^ 2))ˣ) (v : ZMod (p ^ 2)) :
    ∃ h : G, ∀ j : ZMod (p ^ 2),
      conjugate (cyclicLamp a t j) h = cyclicLamp a t ((u : ZMod (p ^ 2)) * j + v) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  obtain ⟨e, he⟩ := unit_is_dyadic hp ho (u : ZMod (p ^ 2)) u.isUnit
  refine ⟨s ^ e * t ^ v.val, ?_⟩
  intro j
  calc
    conjugate (cyclicLamp a t j) (s ^ e * t ^ v.val) =
        conjugate (conjugate (cyclicLamp a t j) (s ^ e)) (t ^ v.val) := by
          simp [conjugate, mul_assoc]
    _ = conjugate (cyclicLamp a t ((2 : ZMod (p ^ 2)) ^ e * j)) (t ^ v.val) := by
      rw [scale_lamp a t s (p ^ 2) ha ht hperiod j e]
    _ = cyclicLamp a t (((2 : ZMod (p ^ 2)) ^ e * j) + (v.val : ZMod (p ^ 2))) :=
      (translate_lamp a t (p ^ 2) hperiod _ _).symm
    _ = cyclicLamp a t ((u : ZMod (p ^ 2)) * j + v) := by
      rw [he, ZMod.natCast_zmod_val]

end SmallPresentationStatements.HostAffine
