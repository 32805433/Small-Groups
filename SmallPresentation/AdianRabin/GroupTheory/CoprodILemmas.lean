module

/-
Ported from `GroupUndecidability/GroupTheory/CoprodILemmas.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: Rewrite local import prefix; Convert to module/public-import/exposed-public-section format; Expose formerly private helpers for module translation.
See `provenance/AdianRabin.json` for original and local source hashes.
-/

public import SmallPresentation.UniversalGroup.Foundations.Coproduct
public import Mathlib.Algebra.Group.Int.TypeTags

@[expose] public section

/-!
# Injectivity lemmas for indexed free products

This file supplies two reusable criteria for injectivity of maps out of an
indexed free product.  The first says that the free product of a family of
injective component maps is injective.  The second reduces injectivity of a
lift to nontriviality on every nonempty normal-form word.
-/

open Function

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*}
variable [∀ i, Group (M i)] [∀ i, Group (N i)]

/-- A lift from an indexed free product is injective if every nonempty
normal-form word has nontrivial image. -/
theorem lift_injective_of_neWord_nontrivial
    {I : Type*} {H : I → Type*} [∀ i, Group (H i)]
    {Q : Type*} [Group Q] (f : ∀ i, H i →* Q)
    (hne : ∀ i j (u : NeWord H i j), lift f u.prod ≠ 1) :
    Injective (lift f) := by
  classical
  apply (injective_iff_map_eq_one (lift f)).mpr
  intro x hx
  let u : Word H := Word.equiv x
  have hprod : u.prod = x := by
    change Word.equiv.symm (Word.equiv x) = x
    exact Word.equiv.symm_apply_apply x
  by_cases hu : u = Word.empty
  · rw [← hprod, hu]
    rfl
  · obtain ⟨i, j, v, hv⟩ := NeWord.of_word u hu
    exfalso
    apply hne i j v
    have hvprod : v.prod = u.prod := by
      unfold NeWord.prod
      exact congrArg Word.prod hv
    rw [hvprod, hprod, hx]

namespace NeWord

variable {I : Type*} {H : I → Type*} [∀ i, Group (H i)]

/-- A one-letter reduced word in an infinite cyclic factor, specified by a
nonzero additive exponent. -/
def singletonZ (i : I) (k : ℤ) (hk : k ≠ 0) :
    NeWord (fun _ : I ↦ Multiplicative ℤ) i i :=
  .singleton (Multiplicative.ofAdd k) (by simpa using hk)

/-- Concatenate two reduced nonempty words whose boundary letters lie in the
same factor but have nontrivial product. -/
def merge {i j l : I} (u : NeWord H i j) (v : NeWord H j l)
    (h : u.last * v.head ≠ 1) : NeWord H i l :=
  match u with
  | .singleton x hx => v.mulHead x (by simpa using h)
  | .append front hne tail =>
      .append front hne (merge tail v (by simpa using h))

@[simp] theorem merge_prod {i j l : I} (u : NeWord H i j)
    (v : NeWord H j l) (h : u.last * v.head ≠ 1) :
    (merge u v h).prod = u.prod * v.prod := by
  induction u with
  | singleton x hx => simp [merge]
  | append front hne tail _ ihTail =>
      simp only [merge, append_prod, ihTail, mul_assoc]

/-- Whether a nonempty reduced word has at least two blocks. -/
def IsAppend {i j : I} : NeWord H i j → Prop
  | .singleton _ _ => False
  | .append _ _ _ => True

theorem cast_start_head {G : Type*} [Group G] {i i' j : I} (h : i = i')
    (w : NeWord (fun _ : I ↦ G) i j) :
    (h ▸ w).head = w.head := by cases h; rfl

theorem cast_start_last {i i' j : I} (h : i = i') (w : NeWord H i j) :
    (h ▸ w).last = w.last := by cases h; rfl

theorem cast_start_prod {i i' j : I} (h : i = i') (w : NeWord H i j) :
    (h ▸ w).prod = w.prod := by cases h; rfl

theorem cast_start_isAppend {i i' j : I} (h : i = i') (w : NeWord H i j) :
    IsAppend (h ▸ w) ↔ IsAppend w := by cases h; rfl

theorem merge_head_of_isAppend_left {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hu : IsAppend u) :
    (merge u v h).head = u.head := by
  cases u with
  | singleton => contradiction
  | append => rfl

theorem merge_last_of_isAppend_right {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hv : IsAppend v) :
    (merge u v h).last = v.last := by
  induction u with
  | singleton =>
      cases v with
      | singleton => contradiction
      | append => rfl
  | append front hne tail _ ihTail => exact ihTail v _ hv

theorem merge_isAppend_of_left {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hu : IsAppend u) :
    IsAppend (merge u v h) := by
  cases u with
  | singleton => contradiction
  | append => trivial

theorem merge_isAppend_of_right {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hv : IsAppend v) :
    IsAppend (merge u v h) := by
  cases u with
  | singleton =>
      cases v with
      | singleton => contradiction
      | append => trivial
  | append => trivial

theorem merge_head_singleton {i j : I} (x : H i) (hx : x ≠ 1)
    (v : NeWord H i j) (h : x * v.head ≠ 1) :
    (merge (.singleton x hx) v h).head = x * v.head := by
  simp [merge]

theorem merge_last_singleton {i j : I} (u : NeWord H i j)
    (y : H j) (hy : y ≠ 1) (h : u.last * y ≠ 1) :
    (merge u (.singleton y hy) h).last = u.last * y := by
  induction u with
  | singleton => rfl
  | append front hne tail _ ihTail => simpa [merge] using ihTail y hy h

/-- The product of a nonempty reduced word in an indexed free product is
nontrivial. -/
theorem prod_ne_one {i j : I} (w : NeWord H i j) : w.prod ≠ 1 := by
  classical
  intro h
  have heq : w.toWord = (Word.empty : Word H) := by
    apply (Word.equiv (M := H)).symm.injective
    change w.prod = 1
    exact h
  have hlist := congrArg Word.toList heq
  exact w.toList_ne_nil (by simpa [toWord] using hlist)

end NeWord

theorem of_int_eq_zpow {I : Type*} (i : I) (k : ℤ) :
    of (i := i) (Multiplicative.ofAdd k) =
      (of (i := i) (Multiplicative.ofAdd 1) :
        CoprodI (fun _ : I ↦ Multiplicative ℤ)) ^ k := by
  rw [← map_zpow]
  congr 1
  simpa using (Int.ofAdd_mul (1 : ℤ) k)

end Monoid.CoprodI

namespace FreeGroup

/-- A nonzero power of the canonical generator of the rank-one free group is
nontrivial. -/
theorem unitGenerator_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    (FreeGroup.of () : FreeGroup Unit) ^ k ≠ 1 := by
  intro h
  apply hk
  calc
    k = freeGroupUnitEquivInt ((FreeGroup.of () : FreeGroup Unit) ^ k) :=
      (freeGroupUnitEquivInt.apply_symm_apply k).symm
    _ = freeGroupUnitEquivInt 1 := congrArg _ h
    _ = 0 := by rfl

end FreeGroup
