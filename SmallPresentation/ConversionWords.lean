module

public import SmallPresentation.PackingWords
public import Mathlib.Tactic.Ring

/-!
# Literal perfectification and normalized central-extension rows

These are the recipes in `eq:dummy`, `eq:S-rows`, `eq:uv`, and
`eq:normalized-rows` of `Proofs.md`. This file proves the exponent calculations
and row counts; it makes no small-cancellation, homology, or embedding assumption.
-/
@[expose] public section

namespace SmallPresentationStatements
namespace Word

@[simp] theorem exponent_append {n : ℕ} (a : Fin n → ℤ) (u v : Word n) :
    exponent a (u ++ v) = exponent a u + exponent a v := by
  simp [exponent]

@[simp] theorem exponent_gen {n : ℕ} (a : Fin n → ℤ) (i : Fin n) :
    exponent a (gen i) = a i := by
  simp [exponent, gen]

@[simp] theorem exponent_inverse {n : ℕ} (a : Fin n → ℤ) (w : Word n) :
    exponent a (inverse w) = -exponent a w := by
  induction w with
  | nil => simp [inverse]
  | cons b w ih =>
    rcases b with ⟨i, s⟩
    cases s <;> simp_all [inverse, List.reverse_cons, List.map_append]

@[simp] theorem exponent_power {n : ℕ} (a : Fin n → ℤ) (w : Word n) (k : ℕ) :
    exponent a (power w k) = (k : ℤ) * exponent a w := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    simp only [power, List.replicate_succ, List.flatten_cons, exponent_append] at *
    rw [ih]
    push_cast
    ring

@[simp] theorem exponent_commutator {n : ℕ} (a : Fin n → ℤ) (u v : Word n) :
    exponent a (commutator u v) = 0 := by
  simp [commutator]

end Word
namespace Conversion
open Word

/-- Concatenate the positive blocks `x y^e` in their specified order. -/
def blocks (es : List ℕ) : Word 2 :=
  es.flatMap fun e ↦ gen 0 ++ power (gen 1) e

theorem exponent_blocks (a : Fin 2 → ℤ) (es : List ℕ) :
    exponent a (blocks es) = (es.length : ℤ) * a 0 + (es.sum : ℤ) * a 1 := by
  induction es with
  | nil => simp [blocks]
  | cons e es ih =>
    simp only [blocks, List.flatMap_cons, exponent_append, exponent_gen, exponent_power] at *
    rw [ih]
    simp only [List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- The source uses one-based labels; `i : Fin k` corresponds to its `i + 1`. -/
def perfectCode {k : ℕ} (i : Fin k) : Word 2 :=
  blocks ((List.range' 1 32).map fun l ↦ 2000 + 32 * (i.val + 1) + l)

def dummyExponents₁ : List ℕ :=
  (List.range' 1 16).flatMap fun j ↦
    [1000 - 10 * j, if j = 16 then 1159 else 1000 + 10 * j]

def dummyExponents₂ : List ℕ :=
  999 :: (List.range' 1 16).flatMap fun j ↦
    [1000 - (10 * j + 3), 1000 + (10 * j + 3)]

def dummy₁ : Word 2 := blocks dummyExponents₁

def dummy₂ : Word 2 := blocks dummyExponents₂

theorem exponent_perfectCode {k : ℕ} (i : Fin k) (a : Fin 2 → ℤ) :
    exponent a (perfectCode i) =
      32 * a 0 + (64528 + 1024 * (i.val + 1) : ℤ) * a 1 := by
  rw [perfectCode, exponent_blocks]
  norm_num [List.range', List.sum_cons, Nat.cast_add, Nat.cast_mul]
  ring_nf
  simp

theorem dummyExponents₁_length_sum :
    dummyExponents₁.length = 32 ∧ dummyExponents₁.sum = 31999 := by decide

theorem dummyExponents₂_length_sum :
    dummyExponents₂.length = 33 ∧ dummyExponents₂.sum = 32999 := by decide

theorem dummyExponents_distinct : (dummyExponents₁ ++ dummyExponents₂).Nodup := by
  decide

theorem dummyExponents_bounds :
    ∀ e ∈ dummyExponents₁ ++ dummyExponents₂, 2 ≤ e ∧ e ≤ 1163 := by decide

theorem perfectCode_exponents_injective {k : ℕ} (i i' : Fin k) (l l' : Fin 32)
    (h : 2000 + 32 * (i.val + 1) + (l.val + 1) =
      2000 + 32 * (i'.val + 1) + (l'.val + 1)) : i = i' ∧ l = l' := by
  constructor <;> apply Fin.ext <;> omega

theorem perfectCode_exponents_above_dummy {k : ℕ} (i : Fin k) (l : Fin 32) :
    1163 < 2000 + 32 * (i.val + 1) + (l.val + 1) := by omega

@[simp] theorem exponent_dummy₁ (a : Fin 2 → ℤ) :
    exponent a dummy₁ = 32 * a 0 + 31999 * a 1 := by
  rw [dummy₁, exponent_blocks, dummyExponents₁_length_sum.1, dummyExponents₁_length_sum.2]
  norm_num

@[simp] theorem exponent_dummy₂ (a : Fin 2 → ℤ) :
    exponent a dummy₂ = 33 * a 0 + 32999 * a 1 := by
  rw [dummy₂, exponent_blocks, dummyExponents₂_length_sum.1, dummyExponents₂_length_sum.2]
  norm_num

theorem dummy_determinant : (32 : ℤ) * 32999 - 33 * 31999 = 1 := by norm_num

/-- Eliminate the old generators using the displayed positive code words. -/
def perfectification {k μ : ℕ} (T : FP k μ) : FP 2 (μ + 2) where
  relator i := if h : i.val < μ then subst perfectCode (T.relator ⟨i.val, h⟩)
    else if i.val = μ then dummy₁ else dummy₂

@[simp] theorem perfectification_dummy₁ {k μ : ℕ} (T : FP k μ) :
    (perfectification T).relator ⟨μ, by omega⟩ = dummy₁ := by
  simp [perfectification]

@[simp] theorem perfectification_dummy₂ {k μ : ℕ} (T : FP k μ) :
    (perfectification T).relator ⟨μ + 1, by omega⟩ = dummy₂ := by
  simp [perfectification]

/-- The literal central word with exponent vector `(1, 0)`. -/
def centralSection₁ : Word 2 :=
  power dummy₁ 32999 ++ inverse (power dummy₂ 31999)

/-- The literal central word with exponent vector `(0, 1)`. -/
def centralSection₂ : Word 2 :=
  inverse (power dummy₁ 33) ++ power dummy₂ 32

@[simp] theorem exponent_centralSection₁ (a : Fin 2 → ℤ) :
    exponent a centralSection₁ = a 0 := by
  simp only [centralSection₁, exponent_append, exponent_inverse, exponent_power,
    exponent_dummy₁, exponent_dummy₂]
  norm_num
  ring

@[simp] theorem exponent_centralSection₂ (a : Fin 2 → ℤ) :
    exponent a centralSection₂ = a 1 := by
  simp only [centralSection₂, exponent_append, exponent_inverse, exponent_power,
    exponent_dummy₁, exponent_dummy₂]
  norm_num
  ring

/-- The exact normalized rows of the quotient of `F/[F,R]` by its central section. -/
def normalizedPresentation {k μ : ℕ} (T : FP k μ) : FP 2 (2 * μ + 6) where
  relator i := if i.val = 0 then centralSection₁ else if i.val = 1 then centralSection₂
    else commutator (gen (if (i.val - 2) % 2 = 0 then 0 else 1))
      ((perfectification T).relator ⟨(i.val - 2) / 2, by omega⟩)

theorem normalizedPresentation_even {k μ : ℕ} (T : FP k μ) (j : Fin (μ + 2)) :
    (normalizedPresentation T).relator ⟨2 * j.val + 2, by omega⟩ =
      commutator (gen 0) ((perfectification T).relator j) := by
  simp [normalizedPresentation]

theorem normalizedPresentation_odd {k μ : ℕ} (T : FP k μ) (j : Fin (μ + 2)) :
    (normalizedPresentation T).relator ⟨2 * j.val + 3, by omega⟩ =
      commutator (gen 1) ((perfectification T).relator j) := by
  have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
  simp [normalizedPresentation, hdiv]

theorem normalizedPresentation_normalized {k μ : ℕ} (T : FP k μ) :
    Normalized (normalizedPresentation T) := by
  refine ⟨by omega, ?_⟩
  intro i
  by_cases h0 : i.val = 0
  · simp only [normalizedPresentation, ite_eq_left h0, exponent_centralSection₁]
    norm_num [h0]
  by_cases h1 : i.val = 1
  · simp only [normalizedPresentation, ite_eq_right h0, ite_eq_left h1, exponent_centralSection₂]
    norm_num
  · simp only [normalizedPresentation, ite_eq_right h0, ite_eq_right h1, exponent_commutator]
    trivial

/-- The universal conversion's literal presentation has exactly 84 row slots. -/
def universalRows (T : FP 6 39) : FP 2 84 := normalizedPresentation T

/-- The torsion-free conversion's literal presentation has exactly 216 row slots. -/
def torsionfreeRows (T : FP 9 105) : FP 2 216 := normalizedPresentation T

theorem universalRows_normalized (T : FP 6 39) : Normalized (universalRows T) :=
  normalizedPresentation_normalized T

theorem torsionfreeRows_normalized (T : FP 9 105) : Normalized (torsionfreeRows T) :=
  normalizedPresentation_normalized T

end Conversion
end SmallPresentationStatements
