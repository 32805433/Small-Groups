module

public import SmallPresentation.MitosisModel
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-! The actual finite mitosis has free abelianization on its two stable letters,
and its source inclusion is zero on abelianization. This calculation uses only
the literal diagonal rows; no homology exact-sequence theorem is needed. -/
@[expose] public section

namespace SmallPresentationStatements.MitosisModel

open Word MitosisWords

variable {n r : ℕ} (P : FP n r)

theorem source_abelianization (x : P.Group) : Abelianization.of (source P x) = 1 := by
  have h := congrArg Abelianization.of (finite_diagonal_action P x)
  simp only [finiteBase_diagonal, finiteSecond_apply, map_mul, map_inv] at h
  have h' : Abelianization.of (source P x) =
      Abelianization.of (source P x) * Abelianization.of (source P x) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  apply mul_left_cancel (a := Abelianization.of (source P x))
  simpa only [mul_one] using h'.symm

theorem source_abelianization_map : Abelianization.map (source P) = 1 := by
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro x
  exact source_abelianization P x

def stableFree : FreeGroup (Fin 2) →* (presentation P).Group :=
  FreeGroup.lift (fun i ↦ PresentedGroup.of (Fin.natAdd n i))

def stableCoordinates : Fin (n + 2) → Abelianization (FreeGroup (Fin 2)) :=
  Fin.addCases (fun _ ↦ 1) (fun i ↦ Abelianization.of (FreeGroup.of i))

theorem stableCoordinates_relator (i : Fin (r + n + n * n)) :
    eval (stableCoordinates (n := n)) ((presentation P).relator i) = 1 := by
  refine Fin.addCases ?_ ?_ i
  · refine Fin.addCases ?_ ?_
    · intro j
      simp only [presentation, Fin.addCases_left, eval_subst, oldGenerator, eval_gen,
        stableCoordinates]
      simp
    · intro j
      simp [presentation, diagonalRow, oldGenerator, stableCoordinates]
  · intro j
    simp [presentation, crossRow, oldGenerator, stableCoordinates]

noncomputable def stableProjection : (presentation P).Group →*
    Abelianization (FreeGroup (Fin 2)) :=
  PresentedGroup.toGroup (f := stableCoordinates (n := n)) (by
    rintro _ ⟨i, rfl⟩
    exact stableCoordinates_relator P i)

@[simp] theorem stableProjection_of (i : Fin (n + 2)) :
    stableProjection P (PresentedGroup.of i) = stableCoordinates i := PresentedGroup.toGroup.of _

noncomputable def abelianizationForward : Abelianization (presentation P).Group →*
    Abelianization (FreeGroup (Fin 2)) := Abelianization.lift (stableProjection P)

noncomputable def abelianizationBackward : Abelianization (FreeGroup (Fin 2)) →*
    Abelianization (presentation P).Group := Abelianization.map (stableFree P)

theorem abelianization_left :
    (abelianizationBackward P).comp (abelianizationForward P) = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply PresentedGroup.ext
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    change abelianizationBackward P (abelianizationForward P
      (Abelianization.of (PresentedGroup.of (Fin.castAdd 2 j)))) =
        Abelianization.of (PresentedGroup.of (Fin.castAdd 2 j))
    simp only [abelianizationForward, Abelianization.lift_apply_of, stableProjection_of,
      stableCoordinates, Fin.addCases_left, map_one]
    exact (source_abelianization P (PresentedGroup.of j)).symm
  · intro j
    change abelianizationBackward P (abelianizationForward P
      (Abelianization.of (PresentedGroup.of (Fin.natAdd n j)))) =
        Abelianization.of (PresentedGroup.of (Fin.natAdd n j))
    simp [abelianizationForward, abelianizationBackward, stableCoordinates, stableFree]

theorem abelianization_right :
    (abelianizationForward P).comp (abelianizationBackward P) = MonoidHom.id _ := by
  apply Abelianization.hom_ext
  apply FreeGroup.ext_hom
  intro i
  simp [abelianizationForward, abelianizationBackward, stableCoordinates, stableFree]

noncomputable def abelianizationFreeEquiv : Abelianization (presentation P).Group ≃*
    Abelianization (FreeGroup (Fin 2)) where
  toFun := abelianizationForward P
  invFun := abelianizationBackward P
  left_inv a := DFunLike.congr_fun (abelianization_left P) a
  right_inv a := DFunLike.congr_fun (abelianization_right P) a
  map_mul' := (abelianizationForward P).map_mul

noncomputable def abelianizationEquiv : Abelianization (presentation P).Group ≃*
    Multiplicative (Fin 2 → ℤ) :=
  (abelianizationFreeEquiv P).trans
    ((MulEquiv.refl _ : Abelianization (FreeGroup (Fin 2)) ≃*
      Multiplicative (FreeAbelianGroup (Fin 2))).trans
      ((FreeAbelianGroup.equivFinsupp (Fin 2)).trans
        ({ Finsupp.equivFunOnFinite with map_add' := fun _ _ ↦ rfl } :
          (Fin 2 →₀ ℤ) ≃+ (Fin 2 → ℤ))).toMultiplicative)

end SmallPresentationStatements.MitosisModel
