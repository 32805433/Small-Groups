module

public import SmallPresentation.PackingAlgebra
public import SmallPresentation.Arithmetic
public import Mathlib.Tactic.Group

/-! # Host actions and separation of the literal dyadic slots -/
@[expose] public section

namespace SmallPresentationStatements.HostAlgebra

open Elimination PackingAlgebra

variable {G : Type*} [Group G]

theorem conjugate_conjugate (a t s : G) :
    conjugate (conjugate a t) s = conjugate (conjugate a s) (conjugate t s) := by
  simp [conjugate, mul_assoc]

theorem conjugate_power (a s : G) (e : ℕ) :
    conjugate (a ^ e) s = (conjugate a s) ^ e := by
  simpa only [MulAut.conj_apply, inv_inv, conjugate] using map_pow (MulAut.conj s⁻¹) a e

theorem conjugate_pow_right (a s : G) (e : ℕ) :
    conjugate a (s ^ (e + 1)) = conjugate (conjugate a (s ^ e)) s := by
  simp [conjugate, pow_succ, mul_assoc]

/-- The actual short support word represents the claimed dyadic lamp index. -/
theorem storedLetter_index (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) (e : ℕ) :
    storedLetter a t s e = conjugate a (t ^ (2 ^ e)) := by
  induction e with
  | zero => simp [storedLetter, conjugate]
  | succ e ih =>
    change conjugate (conjugate a t) (s ^ (e + 1)) = _
    rw [conjugate_pow_right]
    change conjugate (storedLetter a t s e) s = _
    rw [ih, conjugate_conjugate, ha, conjugate_power, ht, ← pow_mul]
    rw [pow_succ, Nat.mul_comm 2]

/-- Conjugating the seed commutator produces each dyadic-distance commutation. -/
theorem commute_dyadic_distance (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) (hseed : Commute a (conjugate a t)) (e : ℕ) :
    Commute a (conjugate a (t ^ (2 ^ e))) := by
  rw [← storedLetter_index a t s ha ht e]
  exact commute_storedLetter ha hseed e

def lamp (a t : G) (i : ℕ) : G := conjugate a (t ^ i)

theorem lamp_add (a t : G) (i j : ℕ) :
    lamp a t (i + j) = conjugate (lamp a t i) (t ^ j) := by
  simp [lamp, conjugate, pow_add, mul_assoc]

/-- Periodicity of the actual lamps, including indices larger than the modulus. -/
theorem lamp_mod (a t : G) (N : ℕ) (hperiod : conjugate a (t ^ N) = a) (i : ℕ) :
    lamp a t (i % N) = lamp a t i := by
  have hfixed : conjugate a (t ^ (N * (i / N))) = a := by
    rw [pow_mul]
    exact fixed_pow hperiod (i / N)
  have hi : N * (i / N) + i % N = i := by
    have h := Nat.mod_add_div i N
    omega
  calc
    lamp a t (i % N) = conjugate (conjugate a (t ^ (N * (i / N)))) (t ^ (i % N)) := by
      rw [hfixed]
      rfl
    _ = lamp a t (N * (i / N) + i % N) := (lamp_add a t _ _).symm
    _ = lamp a t i := congrArg (lamp a t) hi

theorem commute_shifted_dyadic (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) (hseed : Commute a (conjugate a t)) (i e : ℕ) :
    Commute (lamp a t i) (lamp a t (i + 2 ^ e)) := by
  have h := (commute_dyadic_distance a t s ha ht hseed e).conj ((t ^ i)⁻¹)
  simp only [inv_inv] at h
  change Commute (lamp a t i) (conjugate (lamp a t (2 ^ e)) (t ^ i)) at h
  rw [← lamp_add, Nat.add_comm (2 ^ e) i] at h
  exact h

/-- A dyadic residue for the difference gives the required host commutation. -/
theorem commute_lamps_of_dyadic_residue (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) (hseed : Commute a (conjugate a t))
    (N : ℕ) (hperiod : conjugate a (t ^ N) = a) (i j e : ℕ)
    (hres : (i + 2 ^ e) % N = j % N) : Commute (lamp a t i) (lamp a t j) := by
  have h := commute_shifted_dyadic a t s ha ht hseed i e
  rw [← lamp_mod a t N hperiod (i + 2 ^ e), hres, lamp_mod a t N hperiod j] at h
  exact h

theorem order_mod_101 : orderOf (2 : ZMod 101) = 100 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    (Arithmetic.zmod_pow_of_certificate 2 100 101 1 (by decide +kernel))
  intro q hq hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, hd, show (100 : ℕ) ≠ 0 by decide⟩
  have hfac : Nat.primeFactors 100 = {2, 5} := by decide +kernel
  have hcases : q = 2 ∨ q = 5 := by simpa [hfac] using hmem
  rcases hcases with rfl | rfl
  · change (2 : ZMod 101) ^ 50 ≠ 1
    have h : (2 : ZMod 101) ^ 50 = 100 := by
      simpa using Arithmetic.zmod_pow_of_certificate 2 50 101 100 (by decide +kernel)
    rw [h]
    decide
  · change (2 : ZMod 101) ^ 20 ≠ 1
    have h : (2 : ZMod 101) ^ 20 = 95 := by
      simpa using Arithmetic.zmod_pow_of_certificate 2 20 101 95 (by decide +kernel)
    rw [h]
    decide

theorem order_mod_227 : orderOf (2 : ZMod 227) = 226 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    (Arithmetic.zmod_pow_of_certificate 2 226 227 1 (by decide +kernel))
  intro q hq hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, hd, show (226 : ℕ) ≠ 0 by decide⟩
  have hfac : Nat.primeFactors 226 = {2, 113} := by decide +kernel
  have hcases : q = 2 ∨ q = 113 := by simpa [hfac] using hmem
  rcases hcases with rfl | rfl
  · change (2 : ZMod 227) ^ 113 ≠ 1
    have h : (2 : ZMod 227) ^ 113 = 226 := by
      simpa using Arithmetic.zmod_pow_of_certificate 2 113 227 226 (by decide +kernel)
    rw [h]
    decide
  · change (2 : ZMod 227) ^ 2 ≠ 1
    decide

theorem dyadic_residue_injective {p L : ℕ} (hL : L ≤ p - 1)
    (ho : orderOf (2 : ZMod p) = p - 1) :
    Function.Injective (fun i : Fin L ↦ (2 : ZMod p) ^ i.val) := by
  intro i j h
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := (2 : ZMod p)) _ _ h
  · simpa only [Set.mem_Iio, ho] using lt_of_lt_of_le i.isLt hL
  · simpa only [Set.mem_Iio, ho] using lt_of_lt_of_le j.isLt hL

theorem dyadic_pair_same_residue {p : ℕ} (hp : 1 ≤ p)
    (ho : orderOf (2 : ZMod p) = p - 1) (i : ℕ) :
    (2 : ZMod p) ^ i = (2 : ZMod p) ^ (i + p - 1) := by
  have hpow : (2 : ZMod p) ^ (p - 1) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  rw [show i + p - 1 = i + (p - 1) by omega, pow_add, hpow, mul_one]

theorem dyadic_pair_distinct {p L : ℕ} (hp : 3 ≤ p) (hL : L ≤ p - 1)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1)) (i : Fin L) :
    (2 : ZMod (p ^ 2)) ^ i.val ≠ (2 : ZMod (p ^ 2)) ^ (i.val + p - 1) := by
  intro h
  have hbound : 2 * (p - 1) ≤ p * (p - 1) := Nat.mul_le_mul_right _ (by omega)
  have hi : i.val < p - 1 := lt_of_lt_of_le i.isLt hL
  have h₀ : i.val < orderOf (2 : ZMod (p ^ 2)) := by rw [ho]; omega
  have h₁ : i.val + p - 1 < orderOf (2 : ZMod (p ^ 2)) := by rw [ho]; omega
  have heq := pow_injOn_Iio_orderOf (x := (2 : ZMod (p ^ 2))) h₀ h₁ h
  omega

end SmallPresentationStatements.HostAlgebra
