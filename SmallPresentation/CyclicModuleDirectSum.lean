module

public import SmallPresentation.CyclicModuleRegular
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Direct sums of exact periodic modules

The index family may be infinite. Preimages are chosen with support contained
in the support of the original element, so no finiteness hypothesis is needed.
-/

@[expose] public section

namespace SmallPresentationStatements.CyclicModule.Periodic

open DirectSum

universe u v

variable {ι : Type u} {A : ι → Type v} [∀ i, AddCommGroup (A i)]

/-- The coordinatewise periodic complex of an arbitrary direct sum. -/
def directSum (P : ∀ i, Periodic (A i)) : Periodic (⨁ i, A i) where
  difference := DirectSum.map (fun i ↦ (P i).difference)
  norm := DirectSum.map (fun i ↦ (P i).norm)
  difference_norm := by
    intro x
    apply DirectSum.ext
    intro i
    exact (P i).difference_norm (x i)
  norm_difference := by
    intro x
    apply DirectSum.ext
    intro i
    exact (P i).norm_difference (x i)

@[simp]
theorem directSum_difference_apply (P : ∀ i, Periodic (A i)) (x : ⨁ i, A i) (i : ι) :
    (directSum P).difference x i = (P i).difference (x i) := rfl

@[simp]
theorem directSum_norm_apply (P : ∀ i, Periodic (A i)) (x : ⨁ i, A i) (i : ι) :
    (directSum P).norm x i = (P i).norm (x i) := rfl

/-- Even exactness commutes with arbitrary direct sums. -/
theorem directSum_evenExact (P : ∀ i, Periodic (A i))
    (h : ∀ i, (P i).EvenExact) : (directSum P).EvenExact := by
  classical
  intro x hx
  have hx' (i : ι) : (P i).difference (x i) = 0 := DFunLike.congr_fun hx i
  choose y hy using fun i ↦ h i (x i) (hx' i)
  let f (i : ι) (a : A i) : A i := if a = 0 then 0 else y i
  have hf (i : ι) : f i 0 = 0 := by simp [f]
  refine ⟨DFinsupp.mapRange f hf x, ?_⟩
  apply DirectSum.ext
  intro i
  change (P i).norm (f i (x i)) = x i
  by_cases hi : x i = 0
  · simp [f, hi]
  · simpa [f, hi] using hy i

/-- Odd exactness commutes with arbitrary direct sums. -/
theorem directSum_oddExact (P : ∀ i, Periodic (A i))
    (h : ∀ i, (P i).OddExact) : (directSum P).OddExact := by
  classical
  intro x hx
  have hx' (i : ι) : (P i).norm (x i) = 0 := DFunLike.congr_fun hx i
  choose y hy using fun i ↦ h i (x i) (hx' i)
  let f (i : ι) (a : A i) : A i := if a = 0 then 0 else y i
  have hf (i : ι) : f i 0 = 0 := by simp [f]
  refine ⟨DFinsupp.mapRange f hf x, ?_⟩
  apply DirectSum.ext
  intro i
  change (P i).difference (f i (x i)) = x i
  by_cases hi : x i = 0
  · simp [f, hi]
  · simpa [f, hi] using hy i

/-- Any direct sum of regular cyclic modules has vanishing positive periodic cohomology. -/
theorem regular_directSum_exact (n : ℕ) :
    (directSum (fun i ↦ regular (A := A i) n)).EvenExact ∧
      (directSum (fun i ↦ regular (A := A i) n)).OddExact :=
  ⟨directSum_evenExact _ (fun _ ↦ regular_evenExact n),
    directSum_oddExact _ (fun _ ↦ regular_oddExact n)⟩

end SmallPresentationStatements.CyclicModule.Periodic
