module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Certified moduli for packing

The modular exponentiation algorithm reduces after every squaring. Its correctness is proved
before the concrete certificates are checked by kernel reduction; no native decision procedure
is used.
-/
@[expose] public section

namespace SmallPresentationStatements.Arithmetic

def modularPow (a e m : ℕ) : ℕ :=
  if h : e = 0 then 1 % m
  else (modularPow a (e / 2) m ^ 2 * a ^ (e % 2)) % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem modularPow_eq (a e m : ℕ) : modularPow a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    rw [modularPow]
    split
    · next he => subst e; simp
    · next he =>
      rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide))]
      calc
        ((a ^ (e / 2) % m) ^ 2 * a ^ (e % 2)) % m =
            ((a ^ (e / 2)) ^ 2 * a ^ (e % 2)) % m := by
          simp [Nat.mul_mod, Nat.pow_mod]
        _ = a ^ e % m := by
          rw [← pow_mul, ← pow_add]
          congr 2
          omega

theorem zmod_pow_of_certificate (a e m r : ℕ) (h : modularPow a e m = r) :
    (a : ZMod m) ^ e = r := by
  rw [modularPow_eq] at h
  calc
    (a : ZMod m) ^ e = ((a ^ e % m : ℕ) : ZMod m) := by simp
    _ = r := congrArg (fun k : ℕ ↦ (k : ZMod m)) h

theorem prime_101 : Nat.Prime 101 := by decide
set_option maxRecDepth 2048 in
theorem prime_227 : Nat.Prime 227 := by decide

theorem powers_101 :
    (2 : ZMod 10201) ^ 10100 = 1 ∧
    (2 : ZMod 10201) ^ 5050 = 10200 ∧
    (2 : ZMod 10201) ^ 2020 = 4943 ∧
    (2 : ZMod 10201) ^ 100 = 9293 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zmod_pow_of_certificate 2 10100 10201 1 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 5050 10201 10200 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 2020 10201 4943 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 100 10201 9293 (by decide +kernel)

theorem powers_227 :
    (2 : ZMod 51529) ^ 51302 = 1 ∧
    (2 : ZMod 51529) ^ 25651 = 51528 ∧
    (2 : ZMod 51529) ^ 454 = 4317 ∧
    (2 : ZMod 51529) ^ 226 = 45628 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zmod_pow_of_certificate 2 51302 51529 1 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 25651 51529 51528 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 454 51529 4317 (by decide +kernel)
  · exact zmod_pow_of_certificate 2 226 51529 45628 (by decide +kernel)

theorem order_101 : orderOf (2 : ZMod (101 ^ 2)) = 101 * (101 - 1) := by
  change orderOf (2 : ZMod 10201) = 10100
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) powers_101.1
  intro q hq hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, hd, show (10100 : ℕ) ≠ 0 by decide⟩
  have hfac : Nat.primeFactors 10100 = {2, 5, 101} := by decide +kernel
  have hcases : q = 2 ∨ q = 5 ∨ q = 101 := by simpa [hfac] using hmem
  rcases hcases with rfl | rfl | rfl
  · change (2 : ZMod 10201) ^ 5050 ≠ 1
    rw [powers_101.2.1]
    decide
  · change (2 : ZMod 10201) ^ 2020 ≠ 1
    rw [powers_101.2.2.1]
    decide
  · change (2 : ZMod 10201) ^ 100 ≠ 1
    rw [powers_101.2.2.2]
    decide

theorem order_227 : orderOf (2 : ZMod (227 ^ 2)) = 227 * (227 - 1) := by
  change orderOf (2 : ZMod 51529) = 51302
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) powers_227.1
  intro q hq hd
  have hmem := Nat.mem_primeFactors.mpr ⟨hq, hd, show (51302 : ℕ) ≠ 0 by decide⟩
  have hfac : Nat.primeFactors 51302 = {2, 113, 227} := by decide +kernel
  have hcases : q = 2 ∨ q = 113 ∨ q = 227 := by simpa [hfac] using hmem
  rcases hcases with rfl | rfl | rfl
  · change (2 : ZMod 51529) ^ 25651 ≠ 1
    rw [powers_227.2.1]
    decide
  · change (2 : ZMod 51529) ^ 454 ≠ 1
    rw [powers_227.2.2.1]
    decide
  · change (2 : ZMod 51529) ^ 226 ≠ 1
    rw [powers_227.2.2.2]
    decide

end SmallPresentationStatements.Arithmetic
