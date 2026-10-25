module

public import SmallPresentation.MitosisWords
public import SmallPresentation.Computability
public import SmallPresentation.UniversalGroup.Foundations.HNN.Identifying
public import Mathlib.GroupTheory.NoncommCoprod
public import SmallPresentation.HNNTorsion

/-! The literal finite mitosis presentation maps to the actual iterated HNN
extension of `J × J`. Consequently its displayed old generators embed `J`.
The only normal-form input is mathlib's general HNN embedding theorem. -/
@[expose] public section

namespace SmallPresentationStatements.MitosisModel

open Word MitosisWords UniversalGroup

variable (J : Type*) [Group J]

def left : J →* J × J where
  toFun x := (x, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

def right : J →* J × J where
  toFun x := (1, x)
  map_one' := rfl
  map_mul' _ _ := by simp

def diagonal : J →* J × J where
  toFun x := (x, x)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem left_injective : Function.Injective (left J) := fun _ _ h ↦ congrArg Prod.fst h
theorem right_injective : Function.Injective (right J) := fun _ _ h ↦ congrArg Prod.snd h
theorem diagonal_injective : Function.Injective (diagonal J) := fun _ _ h ↦ congrArg Prod.fst h

noncomputable abbrev First := IdentifyingHNN (left J) (diagonal J)
  (left_injective J) (diagonal_injective J)

noncomputable def base₁ : J × J →* First J := IdentifyingHNN.of _ _ _ _

theorem base₁_injective : Function.Injective (base₁ J) :=
  IdentifyingHNN.of_injective _ _ _ _

noncomputable def firstLeft : J →* First J := (base₁ J).comp (left J)
noncomputable def firstRight : J →* First J := (base₁ J).comp (right J)

theorem firstLeft_injective : Function.Injective (firstLeft J) :=
  (base₁_injective J).comp (left_injective J)
theorem firstRight_injective : Function.Injective (firstRight J) :=
  (base₁_injective J).comp (right_injective J)

noncomputable abbrev Model := IdentifyingHNN (firstLeft J) (firstRight J)
  (firstLeft_injective J) (firstRight_injective J)

noncomputable def base₂ : First J →* Model J := IdentifyingHNN.of _ _ _ _

theorem base₂_injective : Function.Injective (base₂ J) :=
  IdentifyingHNN.of_injective _ _ _ _

noncomputable def base : J × J →* Model J := (base₂ J).comp (base₁ J)
noncomputable def inclusion : J →* Model J := (base J).comp (left J)
noncomputable def second : J →* Model J := (base J).comp (right J)

theorem inclusion_injective : Function.Injective (inclusion J) :=
  (base₂_injective J).comp ((base₁_injective J).comp (left_injective J))

noncomputable def d : Model J := base₂ J (IdentifyingHNN.stable
  (left J) (diagonal J) (left_injective J) (diagonal_injective J))
noncomputable def s : Model J := IdentifyingHNN.stable _ _ _ _

theorem swap_action (x : J) : (s J)⁻¹ * inclusion J x * s J = second J x :=
  IdentifyingHNN.conjugates _ _ _ _ x

theorem diagonal_action (x : J) :
    (d J)⁻¹ * inclusion J x * d J = inclusion J x * second J x := by
  have h := congrArg (base₂ J) (IdentifyingHNN.conjugates
    (left J) (diagonal J) (left_injective J) (diagonal_injective J) x)
  simp only [map_mul, map_inv] at h
  change (d J)⁻¹ * inclusion J x * d J = base J (diagonal J x) at h
  rw [h]
  change base J (diagonal J x) = base J (left J x) * base J (right J x)
  rw [← map_mul]
  simp [diagonal, left, right]

theorem copies_commute (x y : J) : Commute (inclusion J x) (second J y) := by
  change Commute (base J (left J x)) (base J (right J y))
  apply Commute.map
  show (x, (1 : J)) * (1, y) = (1, y) * (x, 1)
  simp

variable {n r : ℕ} (P : FP n r)

noncomputable def generators : Fin (n + 2) → Model P.Group :=
  Fin.addCases (fun i ↦ inclusion P.Group (PresentedGroup.of (rels := P.relSet) i))
    (Fin.cases (d P.Group) (fun _ ↦ s P.Group))

@[simp] theorem generators_old (i : Fin n) :
    generators P (Fin.castAdd 2 i) = inclusion P.Group (PresentedGroup.of i) := by
  simp [generators]

@[simp] theorem generators_d : generators P ⟨n, by omega⟩ = d P.Group := by
  change generators P (Fin.natAdd n (0 : Fin 2)) = _
  simp [generators]

@[simp] theorem generators_s : generators P ⟨n + 1, by omega⟩ = s P.Group := by
  change generators P (Fin.natAdd n (1 : Fin 2)) = _
  simp only [generators, Fin.addCases_right]
  rfl

theorem generators_relator (i : Fin (r + n + n * n)) :
    eval (generators P) ((presentation P).relator i) = 1 := by
  refine Fin.addCases ?_ ?_ i
  · refine Fin.addCases ?_ ?_
    · intro j
      simp only [presentation, Fin.addCases_left, eval_subst]
      simp only [oldGenerator, eval_gen, generators_old]
      rw [← map_eval, P.eval_relator, map_one]
    · intro j
      simp only [presentation, Fin.addCases_left, Fin.addCases_right, eval_diagonalRow,
        diagonalLetter, swapLetter, oldGenerator, eval_gen, generators_old,
        generators_d, generators_s, swap_action, diagonal_action, mul_inv_cancel]
  · intro k
    simp only [presentation, Fin.addCases_right, crossRow, eval_commutator,
      oldGenerator, swapLetter, eval_gen, eval_conjugate, generators_old,
      generators_s, swap_action]
    have h := copies_commute P.Group
      (PresentedGroup.of (finProdFinEquiv.symm k).1)
      (PresentedGroup.of (finProdFinEquiv.symm k).2)
    rw [h.inv_left.inv_right.eq]
    simp [mul_assoc]

noncomputable def toModel : (presentation P).Group →* Model P.Group :=
  PresentedGroup.toGroup (f := generators P) (by
    rintro _ ⟨i, rfl⟩
    exact generators_relator P i)

@[simp] theorem toModel_of (i : Fin (n + 2)) :
    toModel P (PresentedGroup.of i) = generators P i := PresentedGroup.toGroup.of _

noncomputable def source : P.Group →* (presentation P).Group :=
  PresentedGroup.toGroup
    (f := fun i ↦ PresentedGroup.of (rels := (presentation P).relSet) (Fin.castAdd 2 i)) (by
      rintro _ ⟨i, rfl⟩
      change eval (fun i ↦ PresentedGroup.of (rels := (presentation P).relSet)
        (Fin.castAdd 2 i)) (P.relator i) = 1
      have h := (presentation P).eval_relator (Fin.castAdd (n * n) (Fin.castAdd n i))
      rw [source_row, eval_subst] at h
      simpa only [oldGenerator, eval_gen] using h)

@[simp] theorem source_of (i : Fin n) :
    source P (PresentedGroup.of i) = PresentedGroup.of (Fin.castAdd 2 i) :=
  PresentedGroup.toGroup.of _

theorem toModel_source : (toModel P).comp (source P) = inclusion P.Group := by
  apply PresentedGroup.ext
  intro i
  simp

theorem source_injective : Function.Injective (source P) := by
  intro x y h
  apply inclusion_injective P.Group
  have heq := DFunLike.congr_fun (toModel_source P)
  exact (heq x).symm.trans ((congrArg (toModel P) h).trans (heq y))

noncomputable def finiteD : (presentation P).Group := PresentedGroup.of ⟨n, by omega⟩
noncomputable def finiteS : (presentation P).Group := PresentedGroup.of ⟨n + 1, by omega⟩

noncomputable def finiteSecond : P.Group →* (presentation P).Group :=
  (MulAut.conj (finiteS P)⁻¹).toMonoidHom.comp (source P)

@[simp] theorem finiteSecond_apply (x : P.Group) :
    finiteSecond P x = (finiteS P)⁻¹ * source P x * finiteS P := by
  simp [finiteSecond]

theorem eval_commute {G : Type*} [Group G] (f : Fin n → G) (y : G)
    (h : ∀ i, Commute (f i) y) (w : Word n) : Commute (eval f w) y := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, b⟩
    cases b
    · simpa only [eval_cons, Bool.false_eq_true, ↓reduceIte] using (h i).inv_left.mul_left ih
    · simpa only [eval_cons, ↓reduceIte] using (h i).mul_left ih

theorem finite_copies_commute (x y : P.Group) :
    Commute (source P x) (finiteSecond P y) := by
  have hgen (i j : Fin n) :
      Commute (source P (PresentedGroup.of i)) (finiteSecond P (PresentedGroup.of j)) := by
    have h := (presentation P).eval_relator
      (Fin.natAdd (r + n) (finProdFinEquiv (i, j)))
    rw [cross_row, eval_crossRow] at h
    simp only [oldGenerator, swapLetter, eval_gen, eval_conjugate] at h
    change (source P (PresentedGroup.of i))⁻¹ * (finiteSecond P (PresentedGroup.of j))⁻¹ *
      source P (PresentedGroup.of i) * finiteSecond P (PresentedGroup.of j) = 1 at h
    have h' : (finiteSecond P (PresentedGroup.of j))⁻¹ * source P (PresentedGroup.of i) *
        finiteSecond P (PresentedGroup.of j) = source P (PresentedGroup.of i) := by
      simpa only [mul_assoc, mul_inv_cancel_left, mul_one] using
        congrArg (fun z ↦ source P (PresentedGroup.of i) * z) h
    show source P (PresentedGroup.of i) * finiteSecond P (PresentedGroup.of j) =
      finiteSecond P (PresentedGroup.of j) * source P (PresentedGroup.of i)
    simpa only [mul_assoc, mul_inv_cancel_left] using
      congrArg (fun z ↦ finiteSecond P (PresentedGroup.of j) * z) h'
  obtain ⟨wx, rfl⟩ := P.exists_word x
  obtain ⟨wy, rfl⟩ := P.exists_word y
  rw [map_eval, map_eval]
  apply eval_commute
  intro i
  exact (eval_commute _ _ (fun j ↦ (hgen i j).symm) wy).symm

noncomputable def finiteBase : P.Group × P.Group →* (presentation P).Group :=
  (source P).noncommCoprod (finiteSecond P) (finite_copies_commute P)

@[simp] theorem finiteBase_left (x : P.Group) :
    finiteBase P (left P.Group x) = source P x := by
  simp [finiteBase, left]

@[simp] theorem finiteBase_right (x : P.Group) :
    finiteBase P (right P.Group x) = finiteSecond P x := by
  simp [finiteBase, right]

@[simp] theorem finiteBase_diagonal (x : P.Group) :
    finiteBase P (diagonal P.Group x) = source P x * finiteSecond P x := rfl

theorem finite_diagonal_action (x : P.Group) :
    (finiteD P)⁻¹ * source P x * finiteD P = finiteBase P (diagonal P.Group x) := by
  have heq : (MulAut.conj (finiteD P)⁻¹).toMonoidHom.comp (source P) =
      (finiteBase P).comp (diagonal P.Group) := by
    apply PresentedGroup.ext
    intro i
    have h := (presentation P).eval_relator (Fin.castAdd (n * n) (Fin.natAdd r i))
    rw [diagonal_row, eval_diagonalRow] at h
    simp only [oldGenerator, diagonalLetter, swapLetter, eval_gen] at h
    rw [mul_inv_eq_one] at h
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, finiteBase_diagonal, finiteSecond_apply, source_of, finiteD, finiteS] using h
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    using DFunLike.congr_fun heq x

noncomputable def fromFirst : First P.Group →* (presentation P).Group :=
  IdentifyingHNN.lift _ _ _ _ (finiteBase P) (finiteD P) (by
    intro x
    rw [finiteBase_left]
    exact finite_diagonal_action P x)

@[simp] theorem fromFirst_base (x : P.Group × P.Group) :
    fromFirst P (base₁ P.Group x) = finiteBase P x := IdentifyingHNN.lift_of _ _ _ _ _ _ _ _

@[simp] theorem fromFirst_stable :
    fromFirst P (IdentifyingHNN.stable
      (left P.Group) (diagonal P.Group) (left_injective P.Group) (diagonal_injective P.Group)) =
        finiteD P := IdentifyingHNN.lift_stable _ _ _ _ _ _ _

noncomputable def fromModel : Model P.Group →* (presentation P).Group :=
  IdentifyingHNN.lift _ _ _ _ (fromFirst P) (finiteS P) (by
    intro x
    change (finiteS P)⁻¹ * fromFirst P (base₁ P.Group (left P.Group x)) * finiteS P =
      fromFirst P (base₁ P.Group (right P.Group x))
    simp)

@[simp] theorem fromModel_base₂ (x : First P.Group) :
    fromModel P (base₂ P.Group x) = fromFirst P x := IdentifyingHNN.lift_of _ _ _ _ _ _ _ _

@[simp] theorem fromModel_s : fromModel P (s P.Group) = finiteS P :=
  IdentifyingHNN.lift_stable _ _ _ _ _ _ _

@[simp] theorem fromModel_d : fromModel P (d P.Group) = finiteD P := by
  simp [d]

@[simp] theorem fromModel_inclusion (x : P.Group) :
    fromModel P (inclusion P.Group x) = source P x := by
  change fromModel P (base₂ P.Group (base₁ P.Group (left P.Group x))) = _
  simp

@[simp] theorem fromModel_second (x : P.Group) :
    fromModel P (second P.Group x) = finiteSecond P x := by
  change fromModel P (base₂ P.Group (base₁ P.Group (right P.Group x))) = _
  simp

theorem fromModel_toModel : (fromModel P).comp (toModel P) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, toModel_of, MonoidHom.id_apply]
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change fromModel P (generators P ⟨n, by omega⟩) = finiteD P
      simp
    · have hk : k = 0 := Fin.eq_zero k
      subst k
      change fromModel P (generators P ⟨n + 1, by omega⟩) = finiteS P
      simp

@[simp] theorem toModel_finiteD : toModel P (finiteD P) = d P.Group := by
  simp [finiteD]

@[simp] theorem toModel_finiteS : toModel P (finiteS P) = s P.Group := by
  simp [finiteS]

@[simp] theorem toModel_source_apply (x : P.Group) :
    toModel P (source P x) = inclusion P.Group x := DFunLike.congr_fun (toModel_source P) x

@[simp] theorem toModel_finiteSecond (x : P.Group) :
    toModel P (finiteSecond P x) = second P.Group x := by
  simp [swap_action]

@[simp] theorem toModel_finiteBase (x : P.Group × P.Group) :
    toModel P (finiteBase P x) = base P.Group x := by
  change toModel P (source P x.1 * finiteSecond P x.2) = _
  rw [map_mul, toModel_source_apply, toModel_finiteSecond]
  change base P.Group (left P.Group x.1) * base P.Group (right P.Group x.2) = _
  rw [← map_mul]
  congr 1
  simp [left, right]

theorem toModel_fromFirst : (toModel P).comp (fromFirst P) = base₂ P.Group := by
  apply IdentifyingHNN.hom_ext (left P.Group) (diagonal P.Group)
    (left_injective P.Group) (diagonal_injective P.Group)
  · intro x
    change toModel P (fromFirst P (base₁ P.Group x)) = base P.Group x
    simp
  · change toModel P (fromFirst P (IdentifyingHNN.stable (left P.Group)
      (diagonal P.Group) (left_injective P.Group) (diagonal_injective P.Group))) = d P.Group
    rw [fromFirst_stable, toModel_finiteD]

theorem toModel_fromModel : (toModel P).comp (fromModel P) = MonoidHom.id _ := by
  apply IdentifyingHNN.hom_ext (firstLeft P.Group) (firstRight P.Group)
    (firstLeft_injective P.Group) (firstRight_injective P.Group)
  · intro x
    change toModel P (fromModel P (base₂ P.Group x)) = base₂ P.Group x
    rw [fromModel_base₂]
    exact DFunLike.congr_fun (toModel_fromFirst P) x
  · change toModel P (fromModel P (s P.Group)) = s P.Group
    simp

/-- The literal finite presentation is precisely the double HNN construction,
not merely a quotient or an abstract group containing the source. -/
noncomputable def presentationEquiv : (presentation P).Group ≃* Model P.Group where
  toFun := toModel P
  invFun := fromModel P
  left_inv x := DFunLike.congr_fun (fromModel_toModel P) x
  right_inv x := DFunLike.congr_fun (toModel_fromModel P) x
  map_mul' := (toModel P).map_mul

theorem model_torsionFree [IsMulTorsionFree J] : IsMulTorsionFree (Model J) := by
  let : IsMulTorsionFree (First J) := HNNTorsion.torsionFree
    (UniversalGroup.rangeEquiv (left J) (diagonal J)
      (left_injective J) (diagonal_injective J))
  exact HNNTorsion.torsionFree (UniversalGroup.rangeEquiv
    (firstLeft J) (firstRight J) (firstLeft_injective J) (firstRight_injective J))

theorem presentation_torsionFree [IsMulTorsionFree P.Group] :
    IsMulTorsionFree (presentation P).Group := by
  let := model_torsionFree P.Group
  exact (presentationEquiv P).injective.isMulTorsionFree (presentationEquiv P).toMonoidHom

end SmallPresentationStatements.MitosisModel
