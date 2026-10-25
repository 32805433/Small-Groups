module

public import SmallPresentation.PackingWords
public import SmallPresentation.Computability
public import SmallPresentation.NormalGeneration

/-! # Cyclic collapse, normal generation, and abelianization of the packed presentations -/
public section

namespace SmallPresentationStatements

open Word

variable {L n : ℕ} {Q : FP 2 L} {G : Type*} [Group G]

@[simp] theorem eval_subst_pair (f : Fin n → G) (u v : Word n) (w : Word 2) :
    eval f (subst ![u, v] w) = eval ![eval f u, eval f v] w := by
  rw [eval_subst]
  congr 1
  funext i
  fin_cases i <;> simp

theorem prod_ofFn_first (hL : 0 < L) (z : G) :
    (List.ofFn fun i : Fin L ↦ if i.val = 0 then z else 1).prod = z := by
  cases L with
  | zero => exact (Nat.not_lt_zero _ hL).elim
  | succ k => simp [List.ofFn_succ, List.ofFn_const]

theorem eval_packedWord_of_eval_t_eq_one (hQ : Normalized Q) (p : ℕ)
    (f : Fin n → G) (a t : Word n) (ht : eval f t = 1) :
    eval f (packedWord Q p a t) = eval f a := by
  simp only [packedWord, eval_flatten, List.map_ofFn, Function.comp_def]
  have hslot (i : Fin L) :
      eval f
        (conjugate
          (subst
            ![subst ![a, conjugate a (power t p)] code₁,
              subst ![a, conjugate a (power t p)] code₂] (Q.relator i))
          (power t i.val)) = if i.val = 0 then eval f a else 1 := by
    simp [-eval_subst, ht, eval_code₁_diagonal, eval_code₂_diagonal, hQ.eval_first]
  simp_rw [hslot]
  exact prod_ofFn_first (lt_of_lt_of_le (by decide) hQ.1) _

theorem eval_dyadicWord_of_commute (hQ : Normalized Q) (p : ℕ)
    (f : Fin n → G) (a t s : Word n) (ht : eval f t = 1)
    (hs : Commute (eval f s) (eval f a)) :
    eval f (dyadicWord Q p a t s) = eval f a := by
  have hc (k : ℕ) : (eval f s ^ k)⁻¹ * eval f a * eval f s ^ k = eval f a :=
    (hs.pow_left k).inv_mul_cancel
  simp only [dyadicWord, eval_flatten, List.map_ofFn, Function.comp_def]
  have hslot (i : Fin L) :
      eval f
        (subst
          ![subst
              ![conjugate (conjugate a t) (power s i.val),
                conjugate (conjugate a t) (power s (i.val + p - 1))] code₁,
            subst
              ![conjugate (conjugate a t) (power s i.val),
                conjugate (conjugate a t) (power s (i.val + p - 1))] code₂]
          (Q.relator i)) = if i.val = 0 then eval f a else 1 := by
    simp [-eval_subst, ht, hc, eval_code₁_diagonal, eval_code₂_diagonal, hQ.eval_first]
  simp_rw [hslot]
  exact prod_ofFn_first (lt_of_lt_of_le (by decide) hQ.1) _

theorem eval_dyadicWord_cyclic (hQ : Normalized Q) (p : ℕ)
    (f : Fin n → G) (a t s : Word n) (ht : eval f t = 1) (d : ℤ)
    (hs : eval f s = eval f a ^ d) :
    eval f (dyadicWord Q p a t s) = eval f a := by
  apply eval_dyadicWord_of_commute hQ p f a t s ht
  rw [hs]
  exact (Commute.refl (eval f a)).zpow_left d

theorem threePresentation_collapse (hQ : Normalized Q) (p : ℕ)
    (f : Fin 2 → G) (hs : f 1 = 1)
    (hr : eval f ((threePresentation Q p).relator 2) = 1) : f 0 = 1 := by
  have ht : eval f eliminatedT = 1 := by simp [eliminatedT, hs]
  have ha : eval f eliminatedA = f 0 := by simp [eliminatedA, ht]
  have hw : eval f (dyadicWord Q p eliminatedA eliminatedT (gen 1)) = f 0 := by
    rw [eval_dyadicWord_of_commute hQ p f _ _ _ ht, ha]
    simp [hs]
  have h : (f 0)⁻¹ = 1 := by simpa [threePresentation, ht, hw] using hr
  exact inv_eq_one.mp h

theorem fourPresentation_collapse (hQ : Normalized Q) (p : ℕ)
    (f : Fin 2 → G) (hs : f 1 = 1)
    (hr : eval f ((fourPresentation Q p).relator 3) = 1) : f 0 = 1 := by
  have ht : eval f eliminatedT = 1 := by simp [eliminatedT, hs]
  have ha : eval f eliminatedA = f 0 := by simp [eliminatedA, ht]
  have hw : eval f (packedWord Q p eliminatedA eliminatedT) = f 0 := by
    rw [eval_packedWord_of_eval_t_eq_one hQ p f _ _ ht, ha]
  simpa [fourPresentation, hw] using hr

/-- A collapse verified in every target group proves normal generation in the presented group. -/
theorem normalGenerator_of_relator_collapse {m : ℕ} (P : FP 2 m) (j : Fin m)
    (hcollapse : ∀ {H : Type} [Group H] (f : Fin 2 → H), f 1 = 1 →
      eval f (P.relator j) = 1 → f 0 = 1) :
    Subgroup.normalClosure
      ({PresentedGroup.of (rels := P.relSet) 1} : Set P.Group) = ⊤ := by
  let N := Subgroup.normalClosure
    ({PresentedGroup.of (rels := P.relSet) 1} : Set P.Group)
  let π : P.Group →* P.Group ⧸ N := QuotientGroup.mk' N
  let f : Fin 2 → P.Group ⧸ N := fun i ↦ π (PresentedGroup.of i)
  have hs : f 1 = 1 := (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_singleton _))
  have hr : eval f (P.relator j) = 1 := by
    rw [show eval f (P.relator j) =
      π (eval (PresentedGroup.of (rels := P.relSet)) (P.relator j)) from
        (map_eval π _ _).symm, P.eval_relator, map_one]
  have hb := hcollapse f hs hr
  apply presented_normalClosure_eq_top
  intro i
  fin_cases i
  · exact hb
  · exact hs

theorem threePresentation_normalGenerator (hQ : Normalized Q) (p : ℕ) :
    Subgroup.normalClosure
      ({PresentedGroup.of (rels := (threePresentation Q p).relSet) 1} :
        Set (threePresentation Q p).Group) = ⊤ := by
  apply normalGenerator_of_relator_collapse (threePresentation Q p) 2
  exact fun f hs hr ↦ threePresentation_collapse hQ p f hs hr

theorem fourPresentation_normalGenerator (hQ : Normalized Q) (p : ℕ) :
    Subgroup.normalClosure
      ({PresentedGroup.of (rels := (fourPresentation Q p).relSet) 1} :
        Set (fourPresentation Q p).Group) = ⊤ := by
  apply normalGenerator_of_relator_collapse (fourPresentation Q p) 3
  exact fun f hs hr ↦ fourPresentation_collapse hQ p f hs hr

theorem threePresentation_integer_relators (hQ : Normalized Q) (p : ℕ) (i : Fin 3) :
    eval (![1, Multiplicative.ofAdd 1] : Fin 2 → Multiplicative ℤ)
      ((threePresentation Q p).relator i) = 1 := by
  let f : Fin 2 → Multiplicative ℤ := ![1, Multiplicative.ofAdd 1]
  have ht : eval f eliminatedT = 1 := by simp [eliminatedT, f]
  have ha : eval f eliminatedA = 1 := by simp [eliminatedA, ht, f]
  have hw : eval f (dyadicWord Q p eliminatedA eliminatedT (gen 1)) = 1 := by
    rw [eval_dyadicWord_of_commute hQ p f _ _ _ ht, ha]
    simp [ha]
  change eval f ((threePresentation Q p).relator i) = 1
  fin_cases i <;> simp [threePresentation, actionRow, commutationRow, ht, ha, hw]

theorem fourPresentation_integer_relators (hQ : Normalized Q) (p : ℕ) (i : Fin 4) :
    eval (![1, Multiplicative.ofAdd 1] : Fin 2 → Multiplicative ℤ)
      ((fourPresentation Q p).relator i) = 1 := by
  let f : Fin 2 → Multiplicative ℤ := ![1, Multiplicative.ofAdd 1]
  have ht : eval f eliminatedT = 1 := by simp [eliminatedT, f]
  have ha : eval f eliminatedA = 1 := by simp [eliminatedA, ht, f]
  have hw : eval f (packedWord Q p eliminatedA eliminatedT) = 1 := by
    rw [eval_packedWord_of_eval_t_eq_one hQ p f _ _ ht, ha]
  change eval f ((fourPresentation Q p).relator i) = 1
  fin_cases i <;> simp [fourPresentation, actionRow, commutationRow, ht, ha, hw]

def threePresentationToInt (hQ : Normalized Q) (p : ℕ) :
    (threePresentation Q p).Group →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := ![1, Multiplicative.ofAdd 1]) (by
    rintro _ ⟨i, rfl⟩
    exact threePresentation_integer_relators hQ p i)

def fourPresentationToInt (hQ : Normalized Q) (p : ℕ) :
    (fourPresentation Q p).Group →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := ![1, Multiplicative.ofAdd 1]) (by
    rintro _ ⟨i, rfl⟩
    exact fourPresentation_integer_relators hQ p i)

theorem threePresentation_abelianization (hQ : Normalized Q) (p : ℕ) :
    Nonempty (Abelianization (threePresentation Q p).Group ≃* Multiplicative ℤ) := by
  apply abelianization_Z_of_normalGenerator (PresentedGroup.of 1)
    (threePresentation_normalGenerator hQ p) (threePresentationToInt hQ p)
  simp [threePresentationToInt]

theorem fourPresentation_abelianization (hQ : Normalized Q) (p : ℕ) :
    Nonempty (Abelianization (fourPresentation Q p).Group ≃* Multiplicative ℤ) := by
  apply abelianization_Z_of_normalGenerator (PresentedGroup.of 1)
    (fourPresentation_normalGenerator hQ p) (fourPresentationToInt hQ p)
  simp [fourPresentationToInt]

theorem threePresentation_hasDisplayedNormalGenerator (hQ : Normalized Q) (p : ℕ) :
    HasDisplayedNormalGenerator (threePresentation Q p) :=
  ⟨1, threePresentation_normalGenerator hQ p⟩

theorem fourPresentation_hasDisplayedNormalGenerator (hQ : Normalized Q) (p : ℕ) :
    HasDisplayedNormalGenerator (fourPresentation Q p) :=
  ⟨1, fourPresentation_normalGenerator hQ p⟩

theorem eval_eliminatedT_of_commute (f : Fin 2 → G) (hc : Commute (f 0) (f 1)) :
    eval f eliminatedT = 1 := by
  simp only [eliminatedT, eval_commutator, eval_gen]
  calc
    (f 0)⁻¹ * (f 1)⁻¹ * f 0 * f 1 = (f 0)⁻¹ * ((f 1)⁻¹ * f 0 * f 1) := by
      simp [mul_assoc]
    _ = 1 := by rw [hc.symm.inv_mul_cancel]; simp

theorem threePresentation_commuting_collapse (hQ : Normalized Q) (p : ℕ)
    (f : Fin 2 → G) (hc : Commute (f 0) (f 1))
    (hr : eval f ((threePresentation Q p).relator 2) = 1) : f 0 = 1 := by
  have ht := eval_eliminatedT_of_commute f hc
  have ha : eval f eliminatedA = f 0 := by simp [eliminatedA, ht]
  have hw : eval f (dyadicWord Q p eliminatedA eliminatedT (gen 1)) = f 0 := by
    rw [eval_dyadicWord_of_commute hQ p f _ _ _ ht, ha]
    simpa [ha] using hc.symm
  have h : (f 0)⁻¹ = 1 := by simpa [threePresentation, ht, hw] using hr
  exact inv_eq_one.mp h

theorem fourPresentation_commuting_collapse (hQ : Normalized Q) (p : ℕ)
    (f : Fin 2 → G) (hc : Commute (f 0) (f 1))
    (hr : eval f ((fourPresentation Q p).relator 3) = 1) : f 0 = 1 := by
  have ht := eval_eliminatedT_of_commute f hc
  have ha : eval f eliminatedA = f 0 := by simp [eliminatedA, ht]
  have hw : eval f (packedWord Q p eliminatedA eliminatedT) = f 0 := by
    rw [eval_packedWord_of_eval_t_eq_one hQ p f _ _ ht, ha]
  simpa [fourPresentation, hw] using hr

theorem threePresentation_cyclic_collapse (hQ : Normalized Q) (p : ℕ) (z : G) (d : ℕ)
    (hr : eval ![z, z ^ d] ((threePresentation Q p).relator 2) = 1) : z = 1 :=
  threePresentation_commuting_collapse hQ p ![z, z ^ d] ((Commute.refl z).pow_right d) hr

theorem fourPresentation_cyclic_collapse (hQ : Normalized Q) (p : ℕ) (z : G) (d : ℕ)
    (hr : eval ![z, z ^ d] ((fourPresentation Q p).relator 3) = 1) : z = 1 :=
  fourPresentation_commuting_collapse hQ p ![z, z ^ d] ((Commute.refl z).pow_right d) hr

theorem threePresentation_b_abelianization (hQ : Normalized Q) (p : ℕ) :
    Abelianization.of (PresentedGroup.of (rels := (threePresentation Q p).relSet) 0) = 1 := by
  let P := threePresentation Q p
  let f : Fin 2 → Abelianization P.Group := fun i ↦ Abelianization.of (PresentedGroup.of i)
  apply threePresentation_commuting_collapse hQ p f (mul_comm _ _)
  rw [show eval f (P.relator 2) =
    Abelianization.of (eval (PresentedGroup.of (rels := P.relSet)) (P.relator 2)) from
      (map_eval Abelianization.of _ _).symm, P.eval_relator, map_one]

theorem fourPresentation_b_abelianization (hQ : Normalized Q) (p : ℕ) :
    Abelianization.of (PresentedGroup.of (rels := (fourPresentation Q p).relSet) 0) = 1 := by
  let P := fourPresentation Q p
  let f : Fin 2 → Abelianization P.Group := fun i ↦ Abelianization.of (PresentedGroup.of i)
  apply fourPresentation_commuting_collapse hQ p f (mul_comm _ _)
  rw [show eval f (P.relator 3) =
    Abelianization.of (eval (PresentedGroup.of (rels := P.relSet)) (P.relator 3)) from
      (map_eval Abelianization.of _ _).symm, P.eval_relator, map_one]

end SmallPresentationStatements
