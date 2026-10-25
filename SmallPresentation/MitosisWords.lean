module

public import SmallPresentation.Words
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Ring

/-!
# Literal finite-mitosis presentations

This file constructs precisely the source rows, `n` diagonal-action rows, and `n²`
cross-commutation rows in `eq:finite-mitosis`, and checks the double-mitosis counts.
The graph-of-groups identification and its normal-form theorem are separate obligations.
-/
@[expose] public section

namespace SmallPresentationStatements.MitosisWords

open Word

variable {n r : ℕ}

def oldGenerator (i : Fin n) : Word (n + 2) := gen (Fin.castAdd 2 i)

def diagonalLetter (n : ℕ) : Word (n + 2) := gen ⟨n, by omega⟩

def swapLetter (n : ℕ) : Word (n + 2) := gen ⟨n + 1, by omega⟩

def diagonalRow (i : Fin n) : Word (n + 2) :=
  conjugate (oldGenerator i) (diagonalLetter n) ++
    inverse (oldGenerator i ++ conjugate (oldGenerator i) (swapLetter n))

def crossRow (i j : Fin n) : Word (n + 2) :=
  commutator (oldGenerator i) (conjugate (oldGenerator j) (swapLetter n))

def presentation (P : FP n r) : FP (n + 2) (r + n + n * n) where
  relator := Fin.addCases
    (Fin.addCases (fun i ↦ subst oldGenerator (P.relator i)) diagonalRow)
    (fun k ↦ crossRow (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

theorem source_row (P : FP n r) (i : Fin r) :
    (presentation P).relator (Fin.castAdd (n * n) (Fin.castAdd n i)) =
      subst oldGenerator (P.relator i) := by simp [presentation]

theorem diagonal_row (P : FP n r) (i : Fin n) :
    (presentation P).relator (Fin.castAdd (n * n) (Fin.natAdd r i)) = diagonalRow i := by
  simp [presentation]

theorem cross_row (P : FP n r) (i j : Fin n) :
    (presentation P).relator (Fin.natAdd (r + n) (finProdFinEquiv (i, j))) =
      crossRow i j := by
  simp only [presentation, Fin.addCases_right]
  exact congrArg (fun v : Fin n × Fin n ↦ crossRow v.1 v.2)
    (finProdFinEquiv.symm_apply_apply (i, j))

theorem eval_diagonalRow {G : Type*} [Group G] (f : Fin (n + 2) → G) (i : Fin n) :
    eval f (diagonalRow i) =
      (eval f (diagonalLetter n))⁻¹ * eval f (oldGenerator i) * eval f (diagonalLetter n) *
        (eval f (oldGenerator i) *
          ((eval f (swapLetter n))⁻¹ * eval f (oldGenerator i) * eval f (swapLetter n)))⁻¹ := by
  simp [diagonalRow]

theorem eval_crossRow {G : Type*} [Group G] (f : Fin (n + 2) → G) (i j : Fin n) :
    eval f (crossRow i j) =
      (eval f (oldGenerator i))⁻¹ *
        (eval f (conjugate (oldGenerator j) (swapLetter n)))⁻¹ *
        eval f (oldGenerator i) * eval f (conjugate (oldGenerator j) (swapLetter n)) := by
  simp [crossRow]

end SmallPresentationStatements.MitosisWords
