module

public import Mathlib.GroupTheory.PresentedGroup

/-!
# Eliminating one generator and one action row

The conjugation convention is `x^g = g⁻¹ * x * g`. The reconstruction
identities below are the two directions of the elimination in `Proofs.md`.
-/
@[expose] public section

namespace SmallPresentationStatements.Elimination

variable {G : Type*} [Group G]

def conjugate (x g : G) : G := g⁻¹ * x * g

def commutator (x g : G) : G := x⁻¹ * g⁻¹ * x * g

def recoveredT (b s : G) : G := commutator b s

def recoveredA (b s : G) : G := b * (recoveredT b s)⁻¹

theorem conjugate_mul (x y g : G) :
    conjugate (x * y) g = conjugate x g * conjugate y g := by
  unfold conjugate
  simp [mul_assoc]

theorem conjugate_inv (x g : G) : conjugate x⁻¹ g = (conjugate x g)⁻¹ := by
  unfold conjugate
  simp [mul_assoc]

theorem conjugate_b (b s : G) : conjugate b s = b * recoveredT b s := by
  unfold conjugate recoveredT commutator
  simp [mul_assoc]

theorem recover_t (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) : recoveredT (a * t) s = t := by
  unfold recoveredT commutator
  rw [show (a * t)⁻¹ * s⁻¹ * (a * t) * s = (a * t)⁻¹ * conjugate (a * t) s by
    simp [conjugate, mul_assoc]]
  rw [conjugate_mul, ha, ht]
  simp [mul_assoc, pow_two]

theorem recover_a (a t s : G) (ha : conjugate a s = a)
    (ht : conjugate t s = t ^ 2) : recoveredA (a * t) s = a := by
  rw [recoveredA, recover_t a t s ha ht]
  simp [mul_assoc]

theorem recoveredA_fixed (b s : G)
    (ht : conjugate (recoveredT b s) s = recoveredT b s ^ 2) :
    conjugate (recoveredA b s) s = recoveredA b s := by
  rw [recoveredA, conjugate_mul, conjugate_b, conjugate_inv, ht]
  simp [mul_assoc, pow_two]

theorem recover_b (b s : G) : recoveredA b s * recoveredT b s = b := by
  unfold recoveredA
  simp [mul_assoc]

/-- Solutions of the two old action equations correspond bijectively to solutions of
the single new equation, retaining the displayed stable letter exactly. -/
def actionEquiv :
    {v : G × G × G // conjugate v.1 v.2.2 = v.1 ∧
      conjugate v.2.1 v.2.2 = v.2.1 ^ 2} ≃
    {v : G × G // conjugate (recoveredT v.1 v.2) v.2 = recoveredT v.1 v.2 ^ 2} where
  toFun v := ⟨(v.1.1 * v.1.2.1, v.1.2.2), by
    rw [recover_t _ _ _ v.2.1 v.2.2]
    exact v.2.2⟩
  invFun v := ⟨(recoveredA v.1.1 v.1.2, recoveredT v.1.1 v.1.2, v.1.2),
    recoveredA_fixed _ _ v.2, v.2⟩
  left_inv v := by
    apply Subtype.ext
    exact Prod.ext (recover_a _ _ _ v.2.1 v.2.2)
      (Prod.ext (recover_t _ _ _ v.2.1 v.2.2) rfl)
  right_inv v := by
    apply Subtype.ext
    exact Prod.ext (recover_b _ _) rfl

@[simp] theorem map_conjugate {H : Type*} [Group H] (f : G →* H) (x g : G) :
    f (conjugate x g) = conjugate (f x) (f g) := by simp [conjugate]

@[simp] theorem map_recoveredT {H : Type*} [Group H] (f : G →* H) (b s : G) :
    f (recoveredT b s) = recoveredT (f b) (f s) := by simp [recoveredT, commutator]

@[simp] theorem map_recoveredA {H : Type*} [Group H] (f : G →* H) (b s : G) :
    f (recoveredA b s) = recoveredA (f b) (f s) := by simp [recoveredA]

section Presentations

abbrev a₃ : FreeGroup (Fin 3) := FreeGroup.of 0
abbrev t₃ : FreeGroup (Fin 3) := FreeGroup.of 1
abbrev s₃ : FreeGroup (Fin 3) := FreeGroup.of 2
abbrev b₂ : FreeGroup (Fin 2) := FreeGroup.of 0
abbrev s₂ : FreeGroup (Fin 2) := FreeGroup.of 1

def eliminationMap : FreeGroup (Fin 3) →* FreeGroup (Fin 2) :=
  FreeGroup.lift fun i ↦ if i.val = 0 then recoveredA b₂ s₂
    else if i.val = 1 then recoveredT b₂ s₂ else s₂

def introductionMap : FreeGroup (Fin 2) →* FreeGroup (Fin 3) :=
  FreeGroup.lift fun i ↦ if i.val = 0 then a₃ * t₃ else s₃

/-- All extra old rows are retained, alongside the two old action rows. -/
def oldRelations (R : Set (FreeGroup (Fin 3))) : Set (FreeGroup (Fin 3)) :=
  R ∪ {conjugate a₃ s₃ * a₃⁻¹, conjugate t₃ s₃ * (t₃ * t₃)⁻¹}

/-- The extra rows are substituted literally, and one new action row is imposed. -/
def newRelations (R : Set (FreeGroup (Fin 3))) : Set (FreeGroup (Fin 2)) :=
  eliminationMap '' R ∪
    {conjugate (recoveredT b₂ s₂) s₂ * (recoveredT b₂ s₂ * recoveredT b₂ s₂)⁻¹}

def descend {α β : Type*} (R : Set (FreeGroup α)) (S : Set (FreeGroup β))
    (f : FreeGroup α →* FreeGroup β) (h : ∀ r ∈ R, PresentedGroup.mk S (f r) = 1) :
    PresentedGroup R →* PresentedGroup S :=
  QuotientGroup.lift (Subgroup.normalClosure R) ((PresentedGroup.mk S).comp f)
    (fun r hr ↦ show ((PresentedGroup.mk S).comp f) r = 1 from
      (Subgroup.normalClosure_le_normal
        (N := ((PresentedGroup.mk S).comp f).ker) h) hr)

@[simp] theorem descend_mk {α β : Type*}
    (R : Set (FreeGroup α)) (S : Set (FreeGroup β))
    (f : FreeGroup α →* FreeGroup β) (h : ∀ r ∈ R, PresentedGroup.mk S (f r) = 1)
    (x : FreeGroup α) : descend R S f h (PresentedGroup.mk R x) = PresentedGroup.mk S (f x) :=
  rfl

theorem old_fixed (R : Set (FreeGroup (Fin 3))) :
    conjugate (PresentedGroup.of (rels := oldRelations R) 0) (PresentedGroup.of 2) =
      PresentedGroup.of 0 := by
  apply mul_inv_eq_one.mp
  simpa [PresentedGroup.of, map_pow, map_zpow, pow_two, zpow_two, a₃, t₃, s₃, b₂, s₂] using
    (PresentedGroup.one_of_mem (rels := oldRelations R)
      (x := conjugate a₃ s₃ * a₃⁻¹) (by simp [oldRelations]))

theorem old_doubling (R : Set (FreeGroup (Fin 3))) :
    conjugate (PresentedGroup.of (rels := oldRelations R) 1) (PresentedGroup.of 2) =
      PresentedGroup.of 1 ^ 2 := by
  apply mul_inv_eq_one.mp
  simpa [PresentedGroup.of, map_pow, map_zpow, pow_two, zpow_two, a₃, t₃, s₃, b₂, s₂] using
    (PresentedGroup.one_of_mem (rels := oldRelations R)
      (x := conjugate t₃ s₃ * (t₃ * t₃)⁻¹) (by simp [oldRelations]))

theorem new_doubling (R : Set (FreeGroup (Fin 3))) :
    conjugate (recoveredT (PresentedGroup.of (rels := newRelations R) 0)
      (PresentedGroup.of 1)) (PresentedGroup.of 1) =
      recoveredT (PresentedGroup.of 0) (PresentedGroup.of 1) ^ 2 := by
  apply mul_inv_eq_one.mp
  simpa [PresentedGroup.of, map_pow, map_zpow, pow_two, zpow_two, a₃, t₃, s₃, b₂, s₂] using
    (PresentedGroup.one_of_mem (rels := newRelations R)
      (x := conjugate (recoveredT b₂ s₂) s₂ * (recoveredT b₂ s₂ * recoveredT b₂ s₂)⁻¹)
      (by simp [newRelations]))

theorem new_reconstruction (r : FreeGroup (Fin 2)) :
    eliminationMap (introductionMap r) = r := by
  have h : eliminationMap.comp introductionMap = MonoidHom.id _ := by
    ext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [eliminationMap, introductionMap, recover_b]
    · have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [eliminationMap, introductionMap]
  exact DFunLike.congr_fun h r

theorem old_reconstruction (R : Set (FreeGroup (Fin 3)))
    (r : FreeGroup (Fin 3)) :
    PresentedGroup.mk (oldRelations R) (introductionMap (eliminationMap r)) =
      PresentedGroup.mk (oldRelations R) r := by
  have h : ((PresentedGroup.mk (oldRelations R)).comp introductionMap).comp eliminationMap =
      PresentedGroup.mk (oldRelations R) := by
    ext i
    refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i) i
    · simpa [eliminationMap, introductionMap, PresentedGroup.of] using
        recover_a _ _ _ (old_fixed R) (old_doubling R)
    · simpa [eliminationMap, introductionMap, PresentedGroup.of] using
        recover_t _ _ _ (old_fixed R) (old_doubling R)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [eliminationMap, introductionMap]
  exact DFunLike.congr_fun h r

theorem elimination_relations (R : Set (FreeGroup (Fin 3)))
    (r : FreeGroup (Fin 3)) (hr : r ∈ oldRelations R) :
    PresentedGroup.mk (newRelations R) (eliminationMap r) = 1 := by
  rcases hr with hr | hr
  · exact PresentedGroup.one_of_mem (Or.inl ⟨r, hr, rfl⟩)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · simpa [eliminationMap, map_pow, pow_two, PresentedGroup.of, a₃, t₃, s₃, b₂, s₂] using
        (mul_inv_eq_one.mpr (recoveredA_fixed _ _ (new_doubling R)))
    · simpa [eliminationMap, map_pow, pow_two, PresentedGroup.of, a₃, t₃, s₃, b₂, s₂] using
        (mul_inv_eq_one.mpr (new_doubling R))

theorem introduction_relations (R : Set (FreeGroup (Fin 3)))
    (r : FreeGroup (Fin 2)) (hr : r ∈ newRelations R) :
    PresentedGroup.mk (oldRelations R) (introductionMap r) = 1 := by
  rcases hr with hr | hr
  · obtain ⟨r, hr, rfl⟩ := hr
    rw [old_reconstruction]
    exact PresentedGroup.one_of_mem (Or.inl hr)
  · obtain rfl := Set.mem_singleton_iff.mp hr
    have h0 : PresentedGroup.mk (oldRelations R) (introductionMap b₂) =
        PresentedGroup.of (rels := oldRelations R) 0 * PresentedGroup.of 1 := by
      simp [introductionMap, PresentedGroup.of]
    have h1 : PresentedGroup.mk (oldRelations R) (introductionMap s₂) =
        PresentedGroup.of (rels := oldRelations R) 2 := by
      simp [introductionMap, PresentedGroup.of]
    simp only [map_mul, map_inv, map_conjugate, map_recoveredT, h0, h1]
    rw [recover_t _ _ _ (old_fixed R) (old_doubling R)]
    simpa only [pow_two] using mul_inv_eq_one.mpr (old_doubling R)

/-- The exact Tietze transformation, with arbitrary additional rows.
The forward map substitutes `(a,t,s) = (A,T,s)` and the inverse sends `b` to `a*t`. -/
def presentationEquiv (R : Set (FreeGroup (Fin 3))) :
    PresentedGroup (oldRelations R) ≃* PresentedGroup (newRelations R) where
  toFun := descend _ _ eliminationMap (elimination_relations R)
  invFun := descend _ _ introductionMap (introduction_relations R)
  map_mul' := map_mul (descend _ _ eliminationMap (elimination_relations R))
  left_inv x := by
    induction x using PresentedGroup.induction_on with
    | H r =>
      simp only [descend_mk]
      exact old_reconstruction R r
  right_inv x := by
    induction x using PresentedGroup.induction_on with
    | H r => simp only [descend_mk, new_reconstruction]

theorem presentationEquiv_stable (R : Set (FreeGroup (Fin 3))) :
    presentationEquiv R (PresentedGroup.of 2) = PresentedGroup.of 1 := by
  change PresentedGroup.mk _ (eliminationMap s₃) = _
  simp [eliminationMap, PresentedGroup.of]

end Presentations

end SmallPresentationStatements.Elimination
