module

public import SmallPresentation.KunnethSplitting
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Algebra.DirectSum.Basic

/-! Canonical maps on Schur multipliers of arbitrary indexed free products.
The direct sum of the factor multipliers embeds by functoriality alone: the
free-product retractions recover every coordinate. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open DirectSum

attribute [local instance] Classical.propDecidable

variable {A : Type} (G : A → Type) [∀ a, Group (G a)]

/-- Kill all free-product factors except the chosen one. -/
noncomputable def freeProductRetraction (a : A) : Monoid.CoprodI G →* G a := by
  classical
  refine Monoid.CoprodI.lift ?_
  intro b
  exact if h : b = a then (by subst b; exact MonoidHom.id _) else 1

@[simp] theorem freeProductRetraction_of (a : A) :
    (freeProductRetraction G a).comp (Monoid.CoprodI.of : G a →* _) = MonoidHom.id _ := by
  classical
  simp [freeProductRetraction]

theorem freeProductRetraction_of_ne (a b : A) (h : b ≠ a) :
    (freeProductRetraction G a).comp (Monoid.CoprodI.of : G b →* _) = 1 := by
  classical
  simp [freeProductRetraction, h]

/-- The canonical homomorphism induced by all free-product factor inclusions. -/
noncomputable def freeProductSchurMap : (⨁ a, H₂ (G a)) →+ H₂ (Monoid.CoprodI G) :=
  DirectSum.toAddMonoid (fun a ↦ map₂ (Monoid.CoprodI.of : G a →* _))

@[simp] theorem freeProductSchurMap_of (a : A) (x : H₂ (G a)) :
    freeProductSchurMap G (DirectSum.of (fun a ↦ H₂ (G a)) a x) =
      map₂ (Monoid.CoprodI.of : G a →* _) x :=
  DirectSum.toAddMonoid_of _ _ _

/-- Evaluation at a factor in the direct sum. -/
def schurComponent (a : A) : (⨁ a, H₂ (G a)) →+ H₂ (G a) where
  toFun x := x a
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical factor retractions recover every coordinate of the Schur direct sum. -/
theorem freeProductSchurMap_retraction (a : A) (x : ⨁ a, H₂ (G a)) :
    map₂ (freeProductRetraction G a) (freeProductSchurMap G x) = x a := by
  classical
  have h : (map₂ (freeProductRetraction G a)).comp (freeProductSchurMap G) =
      schurComponent G a := by
    apply DirectSum.addHom_ext
    intro b z
    change map₂ (freeProductRetraction G a)
      (freeProductSchurMap G (DirectSum.of (fun a ↦ H₂ (G a)) b z)) =
        (DirectSum.of (fun a ↦ H₂ (G a)) b z) a
    rw [freeProductSchurMap_of, map₂_comp]
    by_cases hba : b = a
    · subst b
      rw [freeProductRetraction_of, map₂_id, DirectSum.of_eq_same]
    · rw [freeProductRetraction_of_ne G a b hba, map₂_one,
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hba)]
  exact DFunLike.congr_fun h x

/-- The canonical direct sum of factor Schur multipliers always embeds. -/
theorem freeProductSchurMap_injective : Function.Injective (freeProductSchurMap G) := by
  intro x y h
  apply DFinsupp.ext
  intro a
  have ha := congrArg (map₂ (freeProductRetraction G a)) h
  simpa only [freeProductSchurMap_retraction] using ha

end SmallPresentationStatements.Homology
