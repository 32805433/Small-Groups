module

/-
Ported from `GroupUndecidability/Presentation.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: Rewrite local import prefix; Convert to module/public-import/exposed-public-section format; Replace deprecated if_true/if_false aliases by ite_true/ite_false; Pass f := x explicitly to PresentedGroup.toGroup.
See `provenance/AdianRabin.json` for original and local source hashes.
-/

public import SmallPresentation.UniversalGroup.Foundations.Presentation
public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

namespace UniversalGroup.FP

/-- The word problem for a finite presentation. -/
def wordProblem (P : FP n m) (w : Word n) : Prop :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1

theorem wordProblem_iff_evalWord_eq_one (P : FP n m) (w : Word n) :
    P.wordProblem w ↔ P.evalWord w = 1 := by
  rw [evalWord_eq_mk]
  rfl

/-- A presentation presents the trivial group when every word represents `1`. -/
def presentsTrivial (P : FP n m) : Prop :=
  ∀ w : Word n, P.wordProblem w

theorem presentsTrivial_iff_subsingleton (P : FP n m) :
    P.presentsTrivial ↔ Subsingleton P.Group := by
  constructor
  · intro h
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
    obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
    have hx : PresentedGroup.mk P.relSet x = 1 := by
      rw [← FreeGroup.mk_toWord (x := x)]
      exact h x.toWord
    have hy : PresentedGroup.mk P.relSet y = 1 := by
      rw [← FreeGroup.mk_toWord (x := y)]
      exact h y.toWord
    exact hx.trans hy.symm
  · intro h w
    exact h.elim _ _

/-- A finite presentation is trivial when all of its canonical generators
are equal to one. -/
theorem presentsTrivial_of_generator_eq_one (P : FP n m)
    (h : ∀ i, (PresentedGroup.of i : P.Group) = 1) : P.presentsTrivial := by
  rw [presentsTrivial_iff_subsingleton]
  constructor
  intro a b
  have hmk : PresentedGroup.mk P.relSet =
      (1 : FreeGroup (Fin n) →* P.Group) := by
    apply FreeGroup.ext_hom
    intro i
    simpa [PresentedGroup.of] using h i
  obtain ⟨x, rfl⟩ := PresentedGroup.mk_surjective P.relSet a
  obtain ⟨y, rfl⟩ := PresentedGroup.mk_surjective P.relSet b
  rw [hmk]
  rfl

end UniversalGroup.FP
