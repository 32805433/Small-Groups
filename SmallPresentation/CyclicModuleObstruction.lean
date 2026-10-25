module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.FinCases

/-!
# An elementary obstruction from a two-periodic complex

This module implements the coefficient dimension-shifting argument used in the
torsion-free small-cancellation proof without constructing group cohomology.
It works for arbitrary pairs of additive operators with zero composites.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule

universe u v w z

/-- The two operators of a two-periodic additive complex. -/
structure Periodic (A : Type u) [AddCommGroup A] where
  difference : A →+ A
  norm : A →+ A
  difference_norm : ∀ a, difference (norm a) = 0
  norm_difference : ∀ a, norm (difference a) = 0

namespace Periodic

variable {A : Type u} {B : Type v} {C : Type w} {D : Type z}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]

/-- Vanishing of the positive even cohomology of the periodic complex. -/
def EvenExact (P : Periodic A) : Prop :=
  ∀ a, P.difference a = 0 → ∃ b, P.norm b = a

/-- Vanishing of the odd cohomology of the periodic complex. -/
def OddExact (P : Periodic A) : Prop :=
  ∀ a, P.norm a = 0 → ∃ b, P.difference b = a

theorem evenExact_iff_ker_eq_range (P : Periodic A) :
    P.EvenExact ↔ P.difference.ker = P.norm.range := by
  constructor
  · intro h
    ext a
    constructor
    · exact h a
    · rintro ⟨b, rfl⟩
      exact P.difference_norm b
  · intro h a ha
    change a ∈ P.norm.range
    rw [← h]
    exact ha

theorem oddExact_iff_ker_eq_range (P : Periodic A) :
    P.OddExact ↔ P.norm.ker = P.difference.range := by
  constructor
  · intro h
    ext a
    constructor
    · exact h a
    · rintro ⟨b, rfl⟩
      exact P.norm_difference b
  · intro h a ha
    change a ∈ P.difference.range
    rw [← h]
    exact ha

/-- Compatibility of an additive map with both periodic operators. -/
structure Compatible (P : Periodic A) (Q : Periodic B) (f : A →+ B) : Prop where
  difference : ∀ a, f (P.difference a) = Q.difference (f a)
  norm : ∀ a, f (P.norm a) = Q.norm (f a)

/-- The inverse of an equivariant additive equivalence is equivariant. -/
theorem Compatible.equiv_symm {P : Periodic A} {Q : Periodic B} {e : A ≃+ B}
    (he : Compatible P Q e.toAddMonoidHom) : Compatible Q P e.symm.toAddMonoidHom where
  difference := by
    intro b
    apply e.injective
    calc
      e (e.symm (Q.difference b)) = Q.difference b := e.apply_symm_apply _
      _ = Q.difference (e (e.symm b)) := by rw [e.apply_symm_apply]
      _ = e (P.difference (e.symm b)) := (he.difference _).symm
  norm := by
    intro b
    apply e.injective
    calc
      e (e.symm (Q.norm b)) = Q.norm b := e.apply_symm_apply _
      _ = Q.norm (e (e.symm b)) := by rw [e.apply_symm_apply]
      _ = e (P.norm (e.symm b)) := (he.norm _).symm

/-- Even exactness is preserved by an additive equivalence respecting the operators. -/
theorem evenExact_of_equiv (P : Periodic A) (Q : Periodic B) (e : A ≃+ B)
    (he : Compatible P Q e.toAddMonoidHom) (hP : P.EvenExact) : Q.EvenExact := by
  intro b hb
  have ha : P.difference (e.symm b) = 0 := by
    apply e.injective
    calc
      e (P.difference (e.symm b)) = Q.difference (e (e.symm b)) := he.difference _
      _ = e 0 := by rw [e.apply_symm_apply, hb, map_zero]
  obtain ⟨a, ha⟩ := hP (e.symm b) ha
  refine ⟨e a, ?_⟩
  calc
    Q.norm (e a) = e (P.norm a) := (he.norm a).symm
    _ = b := by rw [ha, e.apply_symm_apply]

/-- Odd exactness is preserved by an additive equivalence respecting the operators. -/
theorem oddExact_of_equiv (P : Periodic A) (Q : Periodic B) (e : A ≃+ B)
    (he : Compatible P Q e.toAddMonoidHom) (hP : P.OddExact) : Q.OddExact := by
  intro b hb
  have ha : P.norm (e.symm b) = 0 := by
    apply e.injective
    calc
      e (P.norm (e.symm b)) = Q.norm (e (e.symm b)) := he.norm _
      _ = e 0 := by rw [e.apply_symm_apply, hb, map_zero]
  obtain ⟨a, ha⟩ := hP (e.symm b) ha
  refine ⟨e a, ?_⟩
  calc
    Q.difference (e a) = e (P.difference a) := (he.difference a).symm
    _ = b := by rw [ha, e.apply_symm_apply]

/-- Two coefficient shifts, proved by lifting elements through an exact sequence.
Only even exactness of the first and third terms and odd exactness of the second
term are needed to obtain even exactness of the final term. -/
theorem evenExact_of_exact_four_term
    (PA : Periodic A) (PB : Periodic B) (PC : Periodic C) (PD : Periodic D)
    (i : A →+ B) (j : B →+ C) (p : C →+ D)
    (hi : Function.Injective i) (hij : j.ker = i.range) (hjp : p.ker = j.range)
    (hp : Function.Surjective p)
    (hiC : Compatible PA PB i) (hjC : Compatible PB PC j)
    (hpC : Compatible PC PD p)
    (hA : PA.EvenExact) (hB : PB.OddExact) (hC : PC.EvenExact) :
    PD.EvenExact := by
  have hji (a : A) : j (i a) = 0 := by
    have h : i a ∈ j.ker := by rw [hij]; exact ⟨a, rfl⟩
    exact h
  have hpj (b : B) : p (j b) = 0 := by
    have h : j b ∈ p.ker := by rw [hjp]; exact ⟨b, rfl⟩
    exact h
  intro d hd
  obtain ⟨c, hc⟩ := hp d
  have hdc : PC.difference c ∈ j.range := by
    rw [← hjp]
    change p (PC.difference c) = 0
    rw [hpC.difference, hc, hd]
  obtain ⟨b, hb⟩ := hdc
  have hnb : PB.norm b ∈ i.range := by
    rw [← hij]
    change j (PB.norm b) = 0
    rw [hjC.norm, hb, PC.norm_difference]
  obtain ⟨a, ha⟩ := hnb
  have hda : PA.difference a = 0 := by
    apply hi
    rw [map_zero, hiC.difference, ha, PB.difference_norm]
  obtain ⟨a', ha'⟩ := hA a hda
  have hnb' : PB.norm (b - i a') = 0 := by
    rw [map_sub, ← hiC.norm, ha', ha, sub_self]
  obtain ⟨b', hb'⟩ := hB (b - i a') hnb'
  have hdc' : PC.difference (c - j b') = 0 := by
    rw [map_sub, ← hjC.difference, hb', map_sub, hji, sub_zero, hb, sub_self]
  obtain ⟨c', hc'⟩ := hC (c - j b') hdc'
  refine ⟨p c', ?_⟩
  rw [← hpC.norm, hc', map_sub, hpj, sub_zero, hc]

/-- The periodic complex of a trivial integer module for a group of order `n`. -/
def integer (n : ℕ) : Periodic ℤ where
  difference := 0
  norm :=
    { toFun := fun x ↦ (n : ℤ) * x
      map_zero' := mul_zero _
      map_add' := fun x y ↦ mul_add _ x y }
  difference_norm := fun _ ↦ rfl
  norm_difference := fun _ ↦ mul_zero _

/-- Even exactness of the trivial integer complex forces the period to be one. -/
theorem integer_evenExact_iff (n : ℕ) : (integer n).EvenExact ↔ n = 1 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h 1 rfl
    have hn : (n : ℤ) ∣ 1 := ⟨x, hx.symm⟩
    have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) hn
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      change (0 : ℤ) * x = 1 at hx
      simp at hx
    omega
  · rintro rfl a _
    exact ⟨a, one_mul a⟩

/-- The exact relation sequence cannot exist with these periodic exactness
properties when its final term is the trivial integer module of period `n>1`. -/
theorem integer_obstruction
    (n : ℕ) (hn : 1 < n)
    (PA : Periodic A) (PB : Periodic B) (PC : Periodic C)
    (i : A →+ B) (j : B →+ C) (p : C →+ ℤ)
    (hi : Function.Injective i) (hij : j.ker = i.range) (hjp : p.ker = j.range)
    (hp : Function.Surjective p)
    (hiC : Compatible PA PB i) (hjC : Compatible PB PC j)
    (hpC : Compatible PC (integer n) p)
    (hA : PA.EvenExact) (hB : PB.OddExact) (hC : PC.EvenExact) : False := by
  have he := evenExact_of_exact_four_term PA PB PC (integer n)
    i j p hi hij hjp hp hiC hjC hpC hA hB hC
  have := (integer_evenExact_iff n).mp he
  omega

end Periodic

end SmallPresentationStatements.CyclicModule
