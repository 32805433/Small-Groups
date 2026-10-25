module

public import SmallPresentation.Words
public import Mathlib.Logic.Equiv.Fin.Basic

/-! The literal five-generator detector, with `r + 6` commutator rows. -/
@[expose] public section

namespace SmallPresentationStatements.Detector

open Word

def x (i : Fin 2) : Word 5 := gen (Fin.castAdd 3 i)
def y (i : Fin 2) : Word 5 := gen (Fin.natAdd 2 (Fin.castAdd 1 i))
def k : Word 5 := gen 4

def presentation {r : ℕ} (P : FP 2 r) : FP 5 (r + 2 + 4) where
  relator := Fin.addCases
    (Fin.addCases (fun j ↦ commutator k (subst x (P.relator j)))
      (fun i ↦ commutator k (x i ++ y i)))
    (fun j ↦ commutator (x ((finProdFinEquiv (m := 2) (n := 2)).symm j).1)
      (y ((finProdFinEquiv (m := 2) (n := 2)).symm j).2))

theorem source_row {r : ℕ} (P : FP 2 r) (j : Fin r) :
    (presentation P).relator (Fin.castAdd 4 (Fin.castAdd 2 j)) =
      commutator k (subst x (P.relator j)) := by simp [presentation]

theorem diagonal_row {r : ℕ} (P : FP 2 r) (i : Fin 2) :
    (presentation P).relator (Fin.castAdd 4 (Fin.natAdd r i)) =
      commutator k (x i ++ y i) := by simp [presentation]

theorem cross_row {r : ℕ} (P : FP 2 r) (i j : Fin 2) :
    (presentation P).relator (Fin.natAdd (r + 2) (finProdFinEquiv (i, j))) =
      commutator (x i) (y j) := by
  simp only [presentation, Fin.addCases_right]
  exact congrArg (fun v : Fin 2 × Fin 2 ↦ commutator (x v.1) (y v.2))
    (finProdFinEquiv.symm_apply_apply (i, j))

def reduction (w : Word 2) : Word 5 := commutator k (subst x w)

theorem reduction_computable : Computable reduction := by
  have h := subst_primrec x
  exact (Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.const (inverse k)) (inverse_primrec.comp h))
      (Primrec.const k)) h).to_comp

end SmallPresentationStatements.Detector
