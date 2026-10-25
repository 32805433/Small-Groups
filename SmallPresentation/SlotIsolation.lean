module

public import SmallPresentation.HostAffine
public import SmallPresentation.PackingKernel

/-! # The actual affine slot-isolation argument for packed rows -/
@[expose] public section

namespace SmallPresentationStatements.SlotIsolation

open Elimination HostAlgebra HostAffine

variable {G : Type*} [Group G] {L : ℕ}

def encodedValue (Q : FP 2 L) (i : Fin L) (x y : G) : G :=
  Word.eval ![x, y] (Word.subst ![code₁, code₂] (Q.relator i))

theorem encodedValue_conjugate (Q : FP 2 L) (i : Fin L) (x y h : G) :
    conjugate (encodedValue Q i x y) h =
      encodedValue Q i (conjugate x h) (conjugate y h) := by
  have heval := Word.map_eval (MulAut.conj h⁻¹).toMonoidHom ![x, y]
    (Word.subst ![code₁, code₂] (Q.relator i))
  have hf : (fun j : Fin 2 ↦ (MulAut.conj h⁻¹) (![x, y] j)) =
      ![conjugate x h, conjugate y h] := by
    funext j
    fin_cases j <;> simp [conjugate]
  simp only [MulEquiv.coe_toMonoidHom] at heval
  rw [hf] at heval
  simpa only [encodedValue, conjugate, MulAut.conj_apply, inv_inv] using heval

theorem encodedValue_commute (Q : FP 2 L) (i : Fin L) (x y z : G)
    (hx : Commute x z) (hy : Commute y z) : Commute (encodedValue Q i x y) z :=
  (PackingAlgebra.commute_pair_eval z x y hx.symm hy.symm _).symm

def storedProduct {V : Type*} (Q : FP 2 L) (lamp : V → G) (u v : Fin L → V) : G :=
  (List.ofFn fun i ↦ encodedValue Q i (lamp (u i)) (lamp (v i))).prod

theorem storedProduct_conjugate {V : Type*} (Q : FP 2 L) (lamp : V → G)
    (u v : Fin L → V) (h : G) (α : V → V)
    (hact : ∀ j, conjugate (lamp j) h = lamp (α j)) :
    conjugate (storedProduct Q lamp u v) h =
      (List.ofFn fun i ↦ encodedValue Q i (lamp (α (u i))) (lamp (α (v i)))).prod := by
  have hmap := map_list_prod (MulAut.conj h⁻¹).toMonoidHom
    (List.ofFn fun i ↦ encodedValue Q i (lamp (u i)) (lamp (v i)))
  simp only [List.map_ofFn] at hmap
  change (MulAut.conj h⁻¹) (storedProduct Q lamp u v) = _ at hmap
  have hh : conjugate (storedProduct Q lamp u v) h =
      (List.ofFn fun i ↦ conjugate (encodedValue Q i (lamp (u i)) (lamp (v i))) h).prod := by
    simpa only [conjugate, MulEquiv.coe_toMonoidHom, Function.comp_def,
      MulAut.conj_apply, inv_inv] using hmap
  simpa only [encodedValue_conjugate, hact] using hh

/-- Affine conjugation isolates every input row against every lamp of the chosen
factor. Cross-factor commutation handles all other lamps. -/
theorem row_commutes_all_lamps (Q : FP 2 L) (a t s : G)
    (ha : conjugate a s = a) (ht : conjugate t s = t ^ 2)
    (hseed : Commute a (conjugate a t)) {p : ℕ} (hp : p.Prime)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (hperiod : conjugate a (t ^ (p ^ 2)) = a)
    (u v : Fin L → ZMod (p ^ 2))
    (hpair : ∀ i, u i ≠ v i ∧ residue p (u i) = residue p (v i))
    (hslots : Function.Injective (fun i ↦ residue p (u i)))
    (hW : ∀ j : ZMod (p ^ 2),
      Commute (storedProduct Q (cyclicLamp a t) u v) (cyclicLamp a t j))
    (i : Fin L) (r z w : ZMod (p ^ 2)) (hrz : r ≠ z)
    (hres : residue p r = residue p z) :
    Commute (encodedValue Q i (cyclicLamp a t r) (cyclicLamp a t z)) (cyclicLamp a t w) := by
  by_cases hrw : residue p r = residue p w
  · obtain ⟨c, b, hcr, hcz⟩ := pair_transitive hp (u i) (v i) r z
      (hpair i).1 hrz (hpair i).2 hres
    obtain ⟨h, hact⟩ := affine_conjugator a t s ha ht hp ho hperiod c b
    let α : ZMod (p ^ 2) → ZMod (p ^ 2) := fun j ↦ (c : ZMod (p ^ 2)) * j + b
    change ∀ j, conjugate (cyclicLamp a t j) h = cyclicLamp a t (α j) at hact
    have honto : Function.Surjective α := by
      intro j
      refine ⟨(↑(c⁻¹) : ZMod (p ^ 2)) * (j - b), ?_⟩
      change (c : ZMod (p ^ 2)) * ((↑(c⁻¹) : ZMod (p ^ 2)) * (j - b)) + b = j
      rw [← mul_assoc]
      have hc : (c : ZMod (p ^ 2)) * ↑(c⁻¹) = 1 :=
        congrArg (fun z : (ZMod (p ^ 2))ˣ ↦ (z : ZMod (p ^ 2))) (mul_inv_cancel c)
      rw [hc, one_mul, sub_add_cancel]
    have htotal : Commute (conjugate (storedProduct Q (cyclicLamp a t) u v) h)
        (cyclicLamp a t w) := by
      obtain ⟨j, hj⟩ := honto w
      have hh := (hW j).conj h⁻¹
      simp only [inv_inv] at hh
      change Commute (conjugate (storedProduct Q (cyclicLamp a t) u v) h)
        (conjugate (cyclicLamp a t j) h) at hh
      rw [hact, hj] at hh
      exact hh
    rw [storedProduct_conjugate Q (cyclicLamp a t) u v h α hact] at htotal
    have hother (j : Fin L) (hji : j ≠ i) :
        Commute (encodedValue Q j (cyclicLamp a t (α (u j)))
          (cyclicLamp a t (α (v j)))) (cyclicLamp a t w) := by
      have huj : residue p (α (u j)) ≠ residue p w := by
        intro heq
        apply hji
        apply hslots
        apply (preserves_residue c b (u j) (u i)).mp
        change residue p (α (u j)) = residue p (α (u i))
        rw [show α (u i) = r from hcr, hrw, heq]
      have hvj : residue p (α (v j)) ≠ residue p w := by
        intro heq
        apply huj
        rw [(preserves_residue c b (u j) (v j)).mpr (hpair j).2]
        exact heq
      exact encodedValue_commute Q j _ _ _
        (cyclicLamp_commute a t s ha ht hseed hp ho hperiod _ _ huj)
        (cyclicLamp_commute a t s ha ht hseed hp ho hperiod _ _ hvj)
    have hselected := PackingKernel.commute_of_stored_product
      (fun j ↦ encodedValue Q j (cyclicLamp a t (α (u j))) (cyclicLamp a t (α (v j))))
      i (cyclicLamp a t w) htotal hother
    simpa only [show α (u i) = r from hcr, show α (v i) = z from hcz] using hselected
  · exact encodedValue_commute Q i _ _ _
      (cyclicLamp_commute a t s ha ht hseed hp ho hperiod r w hrw)
      (cyclicLamp_commute a t s ha ht hseed hp ho hperiod z w
        (show residue p z ≠ residue p w by rw [← hres]; exact hrw))

end SmallPresentationStatements.SlotIsolation
