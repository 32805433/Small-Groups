module

public import SmallPresentation.PackingWords
public import SmallPresentation.Elimination

/-!
# The derived periodicity row

The proof that the absorbed construction has exact period only uses the
fixed-letter action and the initial commutation row. It applies to the literal
`dyadicWord` recipe and does not assume periodicity or a host embedding.
-/
@[expose] public section

namespace SmallPresentationStatements.PackingAlgebra

open Elimination

variable {G : Type*} [Group G]

theorem commute_eval {n : ℕ} (a : G) (f : Fin n → G)
    (hf : ∀ i, Commute a (f i)) (w : Word n) : Commute a (Word.eval f w) := by
  induction w with
  | nil => simp
  | cons v w ih =>
    rw [Word.eval_cons]
    apply Commute.mul_right _ ih
    cases v.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact (hf v.1).inv_right
    · exact hf v.1

theorem fixed_iff_commute (a s : G) : conjugate a s = a ↔ Commute a s := by
  constructor
  · intro h
    have h' := congrArg (fun z ↦ s * z) h
    change a * s = s * a
    simpa [conjugate, mul_assoc] using h'
  · intro h
    exact h.symm.inv_mul_cancel

theorem fixed_pow {a s : G} (h : conjugate a s = a) (e : ℕ) :
    conjugate a (s ^ e) = a :=
  (fixed_iff_commute _ _).mpr (((fixed_iff_commute _ _).mp h).pow_right e)

theorem commutator_eq_one_iff (a b : G) : Elimination.commutator a b = 1 ↔ Commute a b := by
  rw [← fixed_iff_commute]
  constructor
  · intro h
    have h' := congrArg (fun x ↦ a * x) h
    simpa [Elimination.commutator, conjugate, mul_assoc] using h'
  · intro h
    have heq : Elimination.commutator a b = a⁻¹ * conjugate a b := by
      simp [Elimination.commutator, conjugate, mul_assoc]
    rw [heq, h, inv_mul_cancel]

def storedLetter (a t s : G) (e : ℕ) : G := conjugate (conjugate a t) (s ^ e)

theorem commute_storedLetter {a t s : G} (ha : conjugate a s = a)
    (hseed : Commute a (conjugate a t)) (e : ℕ) :
    Commute a (storedLetter a t s e) := by
  have h := hseed.conj ((s ^ e)⁻¹)
  have hfix : (s ^ e)⁻¹ * a * s ^ e = a := fixed_pow ha e
  simpa only [inv_inv, hfix, storedLetter, conjugate] using h

theorem commute_pair_eval (a u v : G) (hu : Commute a u) (hv : Commute a v)
    (w : Word 2) : Commute a (Word.eval ![u, v] w) := by
  apply commute_eval
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact hu
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hv

theorem commute_dyadicWord {L n : ℕ} (Q : FP 2 L) (p : ℕ) (a t s : Word n)
    (f : Fin n → G) (ha : conjugate (Word.eval f a) (Word.eval f s) = Word.eval f a)
    (hseed : Commute (Word.eval f a) (conjugate (Word.eval f a) (Word.eval f t))) :
    Commute (Word.eval f a) (Word.eval f (dyadicWord Q p a t s)) := by
  rw [dyadicWord, Word.eval_flatten]
  apply Commute.list_prod_right
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  simp only [Word.eval_subst]
  apply commute_eval
  intro j
  have hu := commute_storedLetter ha hseed i.val
  have hv := commute_storedLetter ha hseed (i.val + p - 1)
  have hu' : Commute (Word.eval f a)
      (Word.eval f (Word.conjugate (Word.conjugate a t) (Word.power s i.val))) := by
    simpa only [Word.eval_conjugate, Word.eval_power, storedLetter, conjugate] using hu
  have hv' : Commute (Word.eval f a)
      (Word.eval f (Word.conjugate (Word.conjugate a t)
        (Word.power s (i.val + p - 1)))) := by
    simpa only [Word.eval_conjugate, Word.eval_power, storedLetter, conjugate] using hv
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp only [Matrix.cons_val_zero, Word.eval_subst]
    apply commute_eval
    intro k
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · exact hu'
    · have hl : l = 0 := Subsingleton.elim _ _
      subst l
      exact hv'
  · have hk : k = 0 := Subsingleton.elim _ _
    subst k
    simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Word.eval_subst]
    apply commute_eval
    intro k
    refine Fin.cases ?_ (fun l ↦ ?_) k
    · exact hu'
    · have hl : l = 0 := Subsingleton.elim _ _
      subst l
      exact hv' 

/-- The fused row implies exact periodicity; no period relation is assumed. -/
theorem derived_period {L n : ℕ} (Q : FP 2 L) (p N : ℕ) (a t s : Word n)
    (f : Fin n → G) (ha : conjugate (Word.eval f a) (Word.eval f s) = Word.eval f a)
    (hseed : Commute (Word.eval f a) (conjugate (Word.eval f a) (Word.eval f t)))
    (hfused : Word.eval f t ^ N = Word.eval f (dyadicWord Q p a t s)) :
    conjugate (Word.eval f a) (Word.eval f t ^ N) = Word.eval f a := by
  apply (fixed_iff_commute _ _).mpr
  rw [hfused]
  exact commute_dyadicWord Q p a t s f ha hseed

theorem storedLetter_cyclic (z : G) (d : ℤ) (e : ℕ) :
    storedLetter z 1 (z ^ d) e = z := by
  change conjugate (conjugate z 1) ((z ^ d) ^ e) = z
  have h : Commute z ((z ^ d) ^ e) := ((Commute.refl z).zpow_right d).pow_right e
  simpa [conjugate] using h.symm.inv_mul_cancel

end SmallPresentationStatements.PackingAlgebra
