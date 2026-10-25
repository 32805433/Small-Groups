module

public import SmallPresentation.HostAlgebra
public import Mathlib.Data.Nat.Totient

/-! # Primitive dyadic powers reach every cross-residue lamp difference -/
@[expose] public section

namespace SmallPresentationStatements.HostAlgebra

theorem unit_is_dyadic {p : ℕ} (hp : p.Prime)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (x : ZMod (p ^ 2)) (hx : IsUnit x) : ∃ e : ℕ, (2 : ZMod (p ^ 2)) ^ e = x := by
  classical
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hfinite : IsOfFinOrder (2 : ZMod (p ^ 2)) := by
    apply orderOf_pos_iff.mp
    rw [ho]
    exact Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt)
  let u := hfinite.unit
  have hu : orderOf u = p * (p - 1) := by
    rw [← orderOf_units]
    exact ho
  let f : Fin (p * (p - 1)) → (ZMod (p ^ 2))ˣ := fun i ↦ u ^ i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := u) _ _ hij
    · simpa only [Set.mem_Iio, hu] using i.isLt
    · simpa only [Set.mem_Iio, hu] using j.isLt
  have hcard : Fintype.card (Fin (p * (p - 1))) = Fintype.card (ZMod (p ^ 2))ˣ := by
    rw [Fintype.card_fin, ZMod.card_units_eq_totient]
    simpa using (Nat.totient_prime_pow_succ hp 1).symm
  have hs := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).2
  obtain ⟨i, hi⟩ := hs hx.unit
  refine ⟨i.val, ?_⟩
  have h := congrArg Units.val hi
  have huval : (u : ZMod (p ^ 2)) = 2 := rfl
  simpa only [f, Units.val_pow_eq_pow_val, huval, IsUnit.unit_spec] using h

theorem unit_of_prime_reduction_ne_zero {p : ℕ} (hp : p.Prime) (x : ZMod (p ^ 2))
    (hx : ZMod.castHom (show p ∣ p ^ 2 from dvd_pow_self p (by decide)) (ZMod p) x ≠ 0) :
    IsUnit x := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcast : IsUnit (x.val : ZMod (p ^ 2)) := by
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide : 0 < 2)).mpr
    intro hd
    apply hx
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  simpa only [ZMod.natCast_zmod_val] using hcast

/-- All different residue factors commute in the presented host, using only its
four literal relations and the certified order of two. -/
theorem commute_lamps_of_residue_ne {G : Type*} [Group G]
    (a t s : G) (ha : Elimination.conjugate a s = a)
    (ht : Elimination.conjugate t s = t ^ 2)
    (hseed : Commute a (Elimination.conjugate a t))
    {p : ℕ} (hp : p.Prime) (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (hperiod : Elimination.conjugate a (t ^ (p ^ 2)) = a) (i j : ℕ)
    (hij : (i : ZMod p) ≠ (j : ZMod p)) : Commute (lamp a t i) (lamp a t j) := by
  let r := ZMod.castHom (show p ∣ p ^ 2 from dvd_pow_self p (by decide)) (ZMod p)
  have hdiff : IsUnit ((j : ZMod (p ^ 2)) - (i : ZMod (p ^ 2))) := by
    apply unit_of_prime_reduction_ne_zero hp
    change r ((j : ZMod (p ^ 2)) - (i : ZMod (p ^ 2))) ≠ 0
    simpa only [map_sub, map_natCast, sub_ne_zero] using hij.symm
  obtain ⟨e, he⟩ := unit_is_dyadic hp ho _ hdiff
  apply commute_lamps_of_dyadic_residue a t s ha ht hseed (p ^ 2) hperiod i j e
  apply (ZMod.natCast_eq_natCast_iff' (i + 2 ^ e) j (p ^ 2)).mp
  push_cast
  rw [he]
  simp [sub_eq_add_neg]

variable {G : Type*} [Group G]

def cyclicLamp (a t : G) {N : ℕ} (j : ZMod N) : G := lamp a t j.val

theorem cyclicLamp_natCast (a t : G) (N : ℕ) [NeZero N]
    (hperiod : Elimination.conjugate a (t ^ N) = a) (i : ℕ) :
    cyclicLamp a t (i : ZMod N) = lamp a t i := by
  rw [cyclicLamp, ZMod.val_natCast, lamp_mod a t N hperiod]

theorem cyclicLamp_shift (a t : G) (N : ℕ) [NeZero N]
    (hperiod : Elimination.conjugate a (t ^ N) = a) (j : ZMod N) :
    cyclicLamp a t (j + 1) = t⁻¹ * cyclicLamp a t j * t := by
  have hcast : ((j.val + 1 : ℕ) : ZMod N) = j + 1 := by simp
  rw [← hcast, cyclicLamp_natCast a t N hperiod, lamp_add]
  simp only [pow_one, Elimination.conjugate, cyclicLamp]

theorem cyclicLamp_double (a t s : G) (N : ℕ) [NeZero N]
    (ha : Elimination.conjugate a s = a) (ht : Elimination.conjugate t s = t ^ 2)
    (hperiod : Elimination.conjugate a (t ^ N) = a) (j : ZMod N) :
    cyclicLamp a t (2 * j) = s⁻¹ * cyclicLamp a t j * s := by
  have hcast : ((2 * j.val : ℕ) : ZMod N) = 2 * j := by simp
  rw [← hcast, cyclicLamp_natCast a t N hperiod]
  change lamp a t (2 * j.val) = Elimination.conjugate (lamp a t j.val) s
  rw [lamp, lamp, conjugate_conjugate, ha, conjugate_power, ht, ← pow_mul]

theorem cyclicLamp_commute (a t s : G) (ha : Elimination.conjugate a s = a)
    (ht : Elimination.conjugate t s = t ^ 2)
    (hseed : Commute a (Elimination.conjugate a t))
    {p : ℕ} (hp : p.Prime) (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (hperiod : Elimination.conjugate a (t ^ (p ^ 2)) = a) (i j : ZMod (p ^ 2))
    (hij : ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p) i ≠
      ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p) j) :
    Commute (cyclicLamp a t i) (cyclicLamp a t j) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply commute_lamps_of_residue_ne a t s ha ht hseed hp ho hperiod i.val j.val
  simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hij

end SmallPresentationStatements.HostAlgebra
