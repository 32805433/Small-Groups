module

public import SmallPresentation.Computability
public import Mathlib.Data.Fin.VecNotation

/-! # Literal two-generator Gordon attachment and its effectiveness -/
@[expose] public section

namespace SmallPresentationStatements.Gordon

open Word

def alpha : Word 2 := inverse (gen 0) ++ power (gen 1) 2 ++ gen 0

def beta : Word 2 := inverse (gen 1) ++ alpha ++ gen 0 ++ inverse alpha ++ gen 1

def sourceB : Word 2 := gen 0 ++ inverse beta ++ gen 1 ++ beta ++ inverse alpha

def sourceS : Word 2 :=
  power (gen 0) 3 ++ inverse (power beta 2) ++ gen 1 ++ power beta 2 ++ inverse (power alpha 3)

def sourceImages : Fin 2 → Word 2 := ![sourceB, sourceS]

def detector (w : Word 2) : Word 2 :=
  subst sourceImages w ++ power alpha 2 ++ inverse (subst sourceImages w) ++
    inverse (power alpha 2) ++ inverse (power beta 3) ++ inverse (gen 1) ++ power beta 3

/-- The source rows after the four eliminations, with an unused final slot. -/
def sourceRows {m : ℕ} (P : FP 2 m) : Fin (m + 1) → Word 2 :=
  Fin.lastCases [] (fun i ↦ subst sourceImages (P.relator i))

/-- Exactly `m+1` displayed rows, in the order used in the manuscript. -/
def presentation {m : ℕ} (P : FP 2 m) (w : Word 2) : FP 2 (m + 1) where
  relator i := if i.val = m then detector w else sourceRows P i

theorem detector_primrec : Primrec detector := by
  have hw := subst_primrec sourceImages
  have hi := inverse_primrec.comp hw
  exact Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp
            (Primrec.list_append.comp hw (Primrec.const (power alpha 2))) hi)
          (Primrec.const (inverse (power alpha 2))))
        (Primrec.const (inverse (power beta 3))))
      (Primrec.const (inverse (gen 1))))
    (Primrec.const (power beta 3))

theorem presentation_effective {m : ℕ} (P : FP 2 m) :
    Computable₂ fun w i ↦ (presentation P w).relator i := by
  have hc : Primrec fun p : Word 2 × Fin (m + 1) ↦ decide (p.2.val = m) :=
    Primrec.fin_app.comp (Primrec.const fun i : Fin (m + 1) ↦ decide (i.val = m))
      Primrec.snd
  have hs : Primrec fun p : Word 2 × Fin (m + 1) ↦ sourceRows P p.2 :=
    Primrec.fin_app.comp (Primrec.const (sourceRows P)) Primrec.snd
  apply ((Primrec.cond hc (detector_primrec.comp Primrec.fst) hs).to_comp).of_eq
  intro p
  simp only [presentation]
  by_cases h : p.2.val = m <;> simp [h]

theorem family_effective {m : ℕ} (P : FP 2 m) :
    FP.Effective (fun j ↦ presentation P (wordOfNat 2 j)) :=
  (presentation_effective P).comp ((wordOfNat_computable 2).comp Computable.fst)
    Computable.snd

end SmallPresentationStatements.Gordon
