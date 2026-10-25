module

public import SmallPresentation.DetectorModel
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-! All detector rows are commutators. Its abelianization is therefore the
free abelian group on the five displayed generators, with explicit coordinates. -/
@[expose] public section

namespace SmallPresentationStatements.Detector

open Word

variable {r : ℕ} (P : FP 2 r)

theorem commutative_relator {A : Type*} [CommGroup A] (f : Fin 5 → A)
    (i : Fin (r + 2 + 4)) : eval f ((presentation P).relator i) = 1 := by
  have h (u v : Word 5) : eval f (commutator u v) = 1 := by
    rw [eval_commutator]
    exact (commutator_eq_one_iff _ _).mpr (Commute.all _ _)
  refine Fin.addCases ?_ ?_ i
  · refine Fin.addCases ?_ ?_
    · intro j
      rw [source_row]
      exact h _ _
    · intro j
      rw [diagonal_row]
      exact h _ _
  · intro j
    simp only [presentation, Fin.addCases_right]
    exact h _ _

noncomputable def toFreeAbelianization : (presentation P).Group →*
    Abelianization (FreeGroup (Fin 5)) :=
  PresentedGroup.toGroup (f := fun i ↦ Abelianization.of (FreeGroup.of i)) (by
    rintro _ ⟨i, rfl⟩
    exact commutative_relator P _ i)

@[simp] theorem toFreeAbelianization_of (i : Fin 5) :
    toFreeAbelianization P (PresentedGroup.of i) = Abelianization.of (FreeGroup.of i) :=
  PresentedGroup.toGroup.of _

noncomputable def abelianizationForward : Abelianization (presentation P).Group →*
    Abelianization (FreeGroup (Fin 5)) := Abelianization.lift (toFreeAbelianization P)

noncomputable def abelianizationBackward : Abelianization (FreeGroup (Fin 5)) →*
    Abelianization (presentation P).Group := Abelianization.map (PresentedGroup.mk _)

theorem abelianization_left :
    (abelianizationBackward P).comp (abelianizationForward P) = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply PresentedGroup.ext
  intro i
  simp [abelianizationForward, abelianizationBackward]
  rfl

theorem abelianization_right :
    (abelianizationForward P).comp (abelianizationBackward P) = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply FreeGroup.ext_hom
  intro i
  change abelianizationForward P (abelianizationBackward P
    (Abelianization.of (FreeGroup.of i))) = Abelianization.of (FreeGroup.of i)
  change toFreeAbelianization P (PresentedGroup.of i) = _
  exact toFreeAbelianization_of P i

noncomputable def abelianizationFreeEquiv : Abelianization (presentation P).Group ≃*
    Abelianization (FreeGroup (Fin 5)) where
  toFun := abelianizationForward P
  invFun := abelianizationBackward P
  left_inv a := DFunLike.congr_fun (abelianization_left P) a
  right_inv a := DFunLike.congr_fun (abelianization_right P) a
  map_mul' := (abelianizationForward P).map_mul

noncomputable def abelianizationEquiv : Abelianization (presentation P).Group ≃*
    Multiplicative (Fin 5 → ℤ) :=
  (abelianizationFreeEquiv P).trans
    ((MulEquiv.refl _ : Abelianization (FreeGroup (Fin 5)) ≃*
      Multiplicative (FreeAbelianGroup (Fin 5))).trans
      ((FreeAbelianGroup.equivFinsupp (Fin 5)).trans
        ({ Finsupp.equivFunOnFinite with map_add' := fun _ _ ↦ rfl } :
          (Fin 5 →₀ ℤ) ≃+ (Fin 5 → ℤ))).toMultiplicative)

end SmallPresentationStatements.Detector
