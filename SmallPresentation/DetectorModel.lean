module

public import SmallPresentation.DetectorWords
public import SmallPresentation.MitosisModel
public import SmallPresentation.FiberProduct
public import SmallPresentation.UniversalGroup.Foundations.HNN.NormalForms
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-! The detector's literal presentation is the centralizing HNN extension of
two free groups. Britton's lemma therefore gives its exact word-problem reduction. -/
@[expose] public section

namespace SmallPresentationStatements.Detector

open Word UniversalGroup.HNNLemmas

variable {r : ℕ} (P : FP 2 r)

abbrev Free := FreeGroup (Fin 2)
abbrev Base := Free × Free
abbrev D := FiberProduct.presentationSubgroup P
abbrev Model := CentralizerHNN Base (D P)

noncomputable def base : Base →* Model P := centralizerOf (D P)
noncomputable def stable : Model P := centralizerStable (D P)

noncomputable def generators : Fin 5 → Model P :=
  Fin.addCases (m := 2) (n := 3) (fun i ↦ base P (FreeGroup.of i, 1))
    (Fin.addCases (m := 2) (n := 1) (fun i ↦ base P (1, FreeGroup.of i))
      (fun _ ↦ stable P))

@[simp] theorem eval_x (i : Fin 2) : eval (generators P) (x i) =
    base P (FreeGroup.of i, 1) := by simp [x, generators]

@[simp] theorem eval_y (i : Fin 2) : eval (generators P) (y i) =
    base P (1, FreeGroup.of i) := by simp [y, generators]

@[simp] theorem eval_k : eval (generators P) k = stable P := by
  simp only [k, eval_gen]
  change generators P (Fin.natAdd 2 (Fin.natAdd 2 (0 : Fin 1))) = _
  simp only [generators, Fin.addCases_right]

theorem commutator_eq_one_iff {G : Type*} [Group G] (a b : G) :
    a⁻¹ * b⁻¹ * a * b = 1 ↔ Commute a b := by
  have h := commutatorElement_eq_one_iff_commute (g₁ := a⁻¹) (g₂ := b⁻¹)
  simpa only [commutatorElement_def, inv_inv, Commute.inv_inv_iff] using h

theorem eval_subst_x (w : Word 2) :
    eval (generators P) (subst x w) = base P (FreeGroup.mk w, 1) := by
  rw [eval_subst]
  simp only [eval_x]
  let f : Free →* Model P := (base P).comp (MonoidHom.inl Free Free)
  change eval (fun i ↦ f (FreeGroup.of i)) w = f (FreeGroup.mk w)
  rw [← map_eval]
  congr 1
  change FreeGroup.lift FreeGroup.of (FreeGroup.mk w) = _
  rw [FreeGroup.lift_of_eq_id]
  rfl

theorem generators_relator (i : Fin (r + 2 + 4)) :
    eval (generators P) ((presentation P).relator i) = 1 := by
  refine Fin.addCases ?_ ?_ i
  · refine Fin.addCases ?_ ?_
    · intro j
      simp only [presentation, Fin.addCases_left, eval_commutator, eval_k, eval_subst_x]
      apply (commutator_eq_one_iff _ _).mpr
      apply Commute.symm
      apply (centralizerOf_commute_stable_iff (D P) _).mpr
      rw [FiberProduct.presentation_mem_iff, map_one]
      exact PresentedGroup.one_of_mem ⟨j, rfl⟩
    · intro j
      simp only [presentation, Fin.addCases_left, Fin.addCases_right, eval_commutator,
        eval_k, eval_append, eval_x, eval_y]
      rw [← map_mul]
      apply (commutator_eq_one_iff _ _).mpr
      apply Commute.symm
      apply (centralizerOf_commute_stable_iff (D P) _).mpr
      simpa using (FiberProduct.presentation_mem_iff P (FreeGroup.of j)
        (FreeGroup.of j)).mpr rfl
  · intro j
    simp only [presentation, Fin.addCases_right, eval_commutator, eval_x, eval_y]
    apply (commutator_eq_one_iff _ _).mpr
    apply Commute.map
    show (FreeGroup.of _, (1 : Free)) * (1, FreeGroup.of _) =
      (1, FreeGroup.of _) * (FreeGroup.of _, 1)
    simp

noncomputable def toModel : (presentation P).Group →* Model P :=
  PresentedGroup.toGroup (f := generators P) (by
    rintro _ ⟨i, rfl⟩
    exact generators_relator P i)

@[simp] theorem toModel_of (i : Fin 5) :
    toModel P (PresentedGroup.of i) = generators P i := PresentedGroup.toGroup.of _

noncomputable def finiteX : Free →* (presentation P).Group :=
  FreeGroup.lift (fun i ↦ eval (PresentedGroup.of (rels := (presentation P).relSet)) (x i))

noncomputable def finiteY : Free →* (presentation P).Group :=
  FreeGroup.lift (fun i ↦ eval (PresentedGroup.of (rels := (presentation P).relSet)) (y i))

noncomputable def finiteK : (presentation P).Group := PresentedGroup.of 4

theorem finite_copies_commute (a b : Free) : Commute (finiteX P a) (finiteY P b) := by
  have hgen (i j : Fin 2) :
      Commute (finiteX P (FreeGroup.of i)) (finiteY P (FreeGroup.of j)) := by
    have h := (presentation P).eval_relator (Fin.natAdd (r + 2) (finProdFinEquiv (i, j)))
    rw [cross_row, eval_commutator] at h
    exact (commutator_eq_one_iff _ _).mp h
  obtain ⟨wa, rfl⟩ := Quot.exists_rep a
  obtain ⟨wb, rfl⟩ := Quot.exists_rep b
  change Commute (eval _ wa) (eval _ wb)
  apply MitosisModel.eval_commute
  intro i
  apply Commute.symm
  apply MitosisModel.eval_commute
  intro j
  exact (hgen i j).symm

noncomputable def finiteBase : Base →* (presentation P).Group :=
  (finiteX P).noncommCoprod (finiteY P) (finite_copies_commute P)

@[simp] theorem finiteBase_left (a : Free) : finiteBase P (a, 1) = finiteX P a := by
  simp [finiteBase]

@[simp] theorem finiteBase_right (a : Free) : finiteBase P (1, a) = finiteY P a := by
  simp [finiteBase]

theorem finiteK_commutes (a : D P) : Commute (finiteK P) (finiteBase P a) := by
  have hle : D P ≤ (Subgroup.centralizer {finiteK P}).comap (finiteBase P) := by
    apply (Subgroup.closure_le _).mpr
    rintro z (hz | hz)
    · rcases hz with ⟨u, ⟨i, rfl⟩, rfl⟩
      have h := (presentation P).eval_relator (Fin.castAdd 4 (Fin.natAdd r i))
      rw [diagonal_row, eval_commutator] at h
      have hc := (commutator_eq_one_iff _ _).mp h
      change finiteBase P (FreeGroup.of i, FreeGroup.of i) ∈ Subgroup.centralizer {finiteK P}
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa only [finiteBase, MonoidHom.noncommCoprod_apply, finiteX, finiteY,
        FreeGroup.lift_apply_of, eval_append, finiteK, k, eval_gen] using hc.symm.eq
    · rcases hz with ⟨u, ⟨j, rfl⟩, rfl⟩
      have h := (presentation P).eval_relator (Fin.castAdd 4 (Fin.castAdd 2 j))
      rw [source_row, eval_commutator, eval_subst] at h
      have hc := (commutator_eq_one_iff _ _).mp h
      change finiteBase P (FreeGroup.mk (P.relator j), 1) ∈ Subgroup.centralizer {finiteK P}
      rw [finiteBase_left, Subgroup.mem_centralizer_singleton_iff]
      exact hc.symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle a.property)).symm

noncomputable def fromModel : Model P →* (presentation P).Group :=
  HNNExtension.lift (finiteBase P) (finiteK P) (fun a ↦ (finiteK_commutes P a).eq)

@[simp] theorem fromModel_base (a : Base) : fromModel P (base P a) = finiteBase P a :=
  HNNExtension.lift_of _ _ _ _

@[simp] theorem fromModel_stable : fromModel P (stable P) = finiteK P :=
  HNNExtension.lift_t _ _ _

theorem fromModel_toModel : (fromModel P).comp (toModel P) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, toModel_of, MonoidHom.id_apply]
  refine Fin.addCases (m := 2) (n := 3) ?_ ?_ i
  · intro j
    simp [generators, finiteX, x]
  · intro j
    refine Fin.addCases (m := 2) (n := 1) ?_ ?_ j
    · intro l
      simp [generators, finiteY, y]
    · intro l
      have hl : l = 0 := Fin.eq_zero l
      subst l
      exact fromModel_stable P

theorem toModel_injective : Function.Injective (toModel P) := by
  intro a b h
  have heq := DFunLike.congr_fun (fromModel_toModel P)
  exact (heq a).symm.trans ((congrArg (fromModel P) h).trans (heq b))

theorem toModel_finiteX (a : Free) : toModel P (finiteX P a) = base P (a, 1) := by
  have h : (toModel P).comp (finiteX P) = (base P).comp (MonoidHom.inl Free Free) := by
    apply FreeGroup.ext_hom
    intro i
    change toModel P (eval (PresentedGroup.of (rels := (presentation P).relSet)) (x i)) = _
    rw [map_eval]
    simpa only [toModel_of, MonoidHom.comp_apply, MonoidHom.inl_apply] using eval_x P i
  exact DFunLike.congr_fun h a

theorem toModel_finiteY (a : Free) : toModel P (finiteY P a) = base P (1, a) := by
  have h : (toModel P).comp (finiteY P) = (base P).comp (MonoidHom.inr Free Free) := by
    apply FreeGroup.ext_hom
    intro i
    change toModel P (eval (PresentedGroup.of (rels := (presentation P).relSet)) (y i)) = _
    rw [map_eval]
    simpa only [toModel_of, MonoidHom.comp_apply, MonoidHom.inr_apply] using eval_y P i
  exact DFunLike.congr_fun h a

theorem toModel_finiteBase (a : Base) : toModel P (finiteBase P a) = base P a := by
  change toModel P (finiteX P a.1 * finiteY P a.2) = _
  rw [map_mul, toModel_finiteX, toModel_finiteY, ← map_mul]
  congr 1
  simp

theorem toModel_fromModel : (toModel P).comp (fromModel P) = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · ext a
    change toModel P (fromModel P (base P a)) = base P a
    rw [fromModel_base, toModel_finiteBase]
  · change toModel P (fromModel P (stable P)) = stable P
    rw [fromModel_stable]
    exact eval_k P

noncomputable def presentationEquiv : (presentation P).Group ≃* Model P where
  toFun := toModel P
  invFun := fromModel P
  left_inv a := DFunLike.congr_fun (fromModel_toModel P) a
  right_inv a := DFunLike.congr_fun (toModel_fromModel P) a
  map_mul' := (toModel P).map_mul

theorem torsionFree : IsMulTorsionFree (presentation P).Group := by
  let : IsMulTorsionFree (Model P) := HNNTorsion.torsionFree (MulEquiv.refl (D P))
  exact (toModel_injective P).isMulTorsionFree (toModel P)

theorem reduction_correct (w : Word 2) :
    (presentation P).wordProblem (reduction w) ↔ P.wordProblem w := by
  change PresentedGroup.mk _ (FreeGroup.mk _) = 1 ↔ _
  rw [← FP.eval_of]
  rw [← (toModel_injective P).eq_iff]
  rw [map_one, map_eval]
  simp only [toModel_of]
  simp only [reduction, eval_commutator, eval_k, eval_subst_x]
  rw [commutator_eq_one_iff, Commute.symm_iff]
  change Commute (centralizerOf (D P) (FreeGroup.mk w, 1)) (centralizerStable (D P)) ↔ _
  rw [centralizerOf_commute_stable_iff, FiberProduct.detector_mem_iff]

theorem wordProblem_undecidable (hP : ¬ ComputablePred P.wordProblem) :
    ¬ ComputablePred (presentation P).wordProblem := by
  intro h
  apply hP
  exact (computablePred_precomp h reduction_computable).of_eq (reduction_correct P)

end SmallPresentationStatements.Detector
