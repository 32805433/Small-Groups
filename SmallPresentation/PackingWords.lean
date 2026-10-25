module

public import SmallPresentation.Words
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!
# Literal signed codes and packed presentations

The definitions follow `eq:codes`, `eq:final-W`, `eq:dyadic-storage-words`,
`eq:P4-general`, and `eq:three-relator-presentation` in `Proofs.md`.
No embedding or small-cancellation assertion is assumed by these definitions.
-/
@[expose] public section

namespace SmallPresentationStatements

open Word

def code₁ : Word 2 :=
  ((List.range' 2 15).flatMap fun q ↦ gen 0 ++ power (gen 1) q) ++
    gen 0 ++ inverse (power (gen 1) 150)

def code₂ : Word 2 :=
  ((List.range' 17 15).flatMap fun q ↦ gen 0 ++ power (gen 1) q) ++
    gen 0 ++ inverse (power (gen 1) 376)

set_option maxRecDepth 10000 in
theorem code₁_exponents : exponent ![1, 0] code₁ = 16 ∧ exponent ![0, 1] code₁ = -15 := by
  decide

set_option maxRecDepth 10000 in
theorem code₂_exponents : exponent ![1, 0] code₂ = 16 ∧ exponent ![0, 1] code₂ = -16 := by
  decide

set_option maxRecDepth 10000 in
theorem code₁_diagonal_exponent : exponent (fun _ ↦ 1) code₁ = 1 := by decide

set_option maxRecDepth 10000 in
theorem code₂_diagonal_exponent : exponent (fun _ ↦ 1) code₂ = 0 := by decide

theorem eval_code₁_diagonal {G : Type*} [Group G] (z : G) :
    eval ![z, z] code₁ = z := by
  have hf : (![z, z] : Fin 2 → G) = fun _ ↦ z ^ (1 : ℤ) := by
    funext i
    fin_cases i <;> simp
  rw [hf, eval_zpowers, code₁_diagonal_exponent, zpow_one]

theorem eval_code₂_diagonal {G : Type*} [Group G] (z : G) :
    eval ![z, z] code₂ = 1 := by
  have hf : (![z, z] : Fin 2 → G) = fun _ ↦ z ^ (1 : ℤ) := by
    funext i
    fin_cases i <;> simp
  rw [hf, eval_zpowers, code₂_diagonal_exponent, zpow_zero]

/-- The source's literal exponent normalization, indexed from zero. -/
def Normalized {L : ℕ} (Q : FP 2 L) : Prop :=
  2 ≤ L ∧ ∀ i,
    exponent ![1, 0] (Q.relator i) = (if i.val = 0 then 1 else 0) ∧
    exponent ![0, 1] (Q.relator i) = (if i.val = 1 then 1 else 0)

theorem Normalized.eval_first {L : ℕ} {Q : FP 2 L} (hQ : Normalized Q)
    {G : Type*} [Group G] (z : G) (i : Fin L) :
    eval ![z, 1] (Q.relator i) = if i.val = 0 then z else 1 := by
  have hf : (![z, 1] : Fin 2 → G) = fun k ↦ z ^ (![1, 0] : Fin 2 → ℤ) k := by
    funext k
    fin_cases k <;> simp
  rw [hf, eval_zpowers, (hQ.2 i).1]
  split <;> simp

def packedWord {L n : ℕ} (Q : FP 2 L) (p : ℕ) (a t : Word n) : Word n :=
  let x := subst ![a, conjugate a (power t p)] code₁
  let y := subst ![a, conjugate a (power t p)] code₂
  (List.ofFn fun i : Fin L ↦ conjugate (subst ![x, y] (Q.relator i)) (power t i.val)).flatten

def dyadicWord {L n : ℕ} (Q : FP 2 L) (p : ℕ) (a t s : Word n) : Word n :=
  (List.ofFn fun i : Fin L ↦
    let u := conjugate (conjugate a t) (power s i.val)
    let v := conjugate (conjugate a t) (power s (i.val + p - 1))
    subst ![subst ![u, v] code₁, subst ![u, v] code₂] (Q.relator i)).flatten

def eliminatedT : Word 2 := commutator (gen 0) (gen 1)

def eliminatedA : Word 2 := gen 0 ++ inverse eliminatedT

def actionRow : Word 2 :=
  conjugate eliminatedT (gen 1) ++ inverse (power eliminatedT 2)

def commutationRow : Word 2 :=
  commutator eliminatedA (conjugate eliminatedA eliminatedT)

def threePresentation {L : ℕ} (Q : FP 2 L) (p : ℕ) : FP 2 3 where
  relator := ![actionRow, commutationRow,
    power eliminatedT (p ^ 2) ++ inverse (dyadicWord Q p eliminatedA eliminatedT (gen 1))]

def fourPresentation {L : ℕ} (Q : FP 2 L) (p : ℕ) : FP 2 4 where
  relator := ![actionRow,
    conjugate eliminatedA (power eliminatedT (p ^ 2)) ++ inverse eliminatedA,
    commutationRow, packedWord Q p eliminatedA eliminatedT]

end SmallPresentationStatements
