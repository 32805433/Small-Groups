module

public import SmallPresentation.HostPartition
public import SmallPresentation.HostBaumslagSolitar
public import SmallPresentation.Computability
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic

/-! The unsigned host model: the partition product of free groups, acted on
by translation and doubling through the actual Baumslag–Solitar group. -/
@[expose] public section

namespace SmallPresentationStatements.Host

variable (p : ℕ)

def residue : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p (by omega)) _

abbrev Kernel := HostPartition.Group (residue p)

def shiftPerm : Equiv.Perm (ZMod (p ^ 2)) where
  toFun v := v + 1
  invFun v := v - 1
  left_inv v := by simp
  right_inv v := by simp

theorem shift_partition (v w : ZMod (p ^ 2)) :
    residue p (shiftPerm p v) = residue p (shiftPerm p w) ↔ residue p v = residue p w := by
  simp [shiftPerm]

def shift : MulAut (Kernel p) := HostPartition.permAut (residue p) (shiftPerm p) (shift_partition p)

variable (u : (ZMod (p ^ 2))ˣ)

def doublePerm : Equiv.Perm (ZMod (p ^ 2)) where
  toFun v := (u : ZMod (p ^ 2)) * v
  invFun v := (↑u⁻¹ : ZMod (p ^ 2)) * v
  left_inv v := by simp [← mul_assoc]
  right_inv v := by simp [← mul_assoc]

theorem double_partition (v w : ZMod (p ^ 2)) :
    residue p (doublePerm p u v) = residue p (doublePerm p u w) ↔
      residue p v = residue p w := by
  simp only [doublePerm, Equiv.coe_fn_mk, map_mul]
  exact (Units.map (residue p).toMonoidHom u).mul_right_inj

def doubling : MulAut (Kernel p) :=
  HostPartition.permAut (residue p) (doublePerm p u) (double_partition p u)

def lamp (v : ZMod (p ^ 2)) : Kernel p := HostPartition.generator (residue p) v

@[simp] theorem shift_lamp (v : ZMod (p ^ 2)) : shift p (lamp p v) = lamp p (v + 1) :=
  HostPartition.permAut_generator _ _ _ _

@[simp] theorem shift_inv_lamp (v : ZMod (p ^ 2)) : (shift p)⁻¹ (lamp p v) = lamp p (v - 1) :=
  HostPartition.permAut_inv_generator _ _ _ _

@[simp] theorem doubling_lamp (v : ZMod (p ^ 2)) :
    doubling p u (lamp p v) = lamp p (u * v) := HostPartition.permAut_generator _ _ _ _

@[simp] theorem doubling_inv_lamp (v : ZMod (p ^ 2)) :
    (doubling p u)⁻¹ (lamp p v) = lamp p (u⁻¹ * v) :=
  HostPartition.permAut_inv_generator _ _ _ _

variable (hu : (u : ZMod (p ^ 2)) = 2)

include hu in
theorem action_relation :
    ((doubling p u)⁻¹)⁻¹ * (shift p)⁻¹ * (doubling p u)⁻¹ = ((shift p)⁻¹) ^ 2 := by
  apply MulEquiv.toMonoidHom_injective
  apply PresentedGroup.ext
  intro v
  change doubling p u ((shift p)⁻¹ ((doubling p u)⁻¹ (lamp p v))) =
    (shift p)⁻¹ ((shift p)⁻¹ (lamp p v))
  simp only [doubling_inv_lamp, shift_inv_lamp, doubling_lamp]
  congr 1
  rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one, hu]
  ring

noncomputable def action : HostBS.Group →* MulAut (Kernel p) :=
  HostBS.lift (shift p)⁻¹ (doubling p u)⁻¹ (action_relation p u hu)

@[simp] theorem action_t : action p u hu HostBS.t = (shift p)⁻¹ := HostBS.lift_t _ _ _
@[simp] theorem action_s : action p u hu HostBS.s = (doubling p u)⁻¹ := HostBS.lift_s _ _ _

noncomputable abbrev Model := Kernel p ⋊[action p u hu] HostBS.Group

noncomputable def a : Model p u hu := SemidirectProduct.inl (lamp p 0)
noncomputable def t : Model p u hu := SemidirectProduct.inr HostBS.t
noncomputable def s : Model p u hu := SemidirectProduct.inr HostBS.s

theorem lamp_t (v : ZMod (p ^ 2)) :
    (t p u hu)⁻¹ * SemidirectProduct.inl (lamp p v) * t p u hu =
      SemidirectProduct.inl (lamp p (v + 1)) := by
  simpa only [t, action_t, inv_inv, shift_lamp, map_inv] using
    (SemidirectProduct.inl_aut_inv (φ := action p u hu) HostBS.t (lamp p v)).symm

theorem lamp_s (v : ZMod (p ^ 2)) :
    (s p u hu)⁻¹ * SemidirectProduct.inl (lamp p v) * s p u hu =
      SemidirectProduct.inl (lamp p (2 * v)) := by
  simpa only [s, action_s, inv_inv, doubling_lamp, hu, map_inv] using
    (SemidirectProduct.inl_aut_inv (φ := action p u hu) HostBS.s (lamp p v)).symm

theorem a_s : (s p u hu)⁻¹ * a p u hu * s p u hu = a p u hu := by
  simpa only [a, mul_zero] using lamp_s p u hu 0

theorem t_s : (s p u hu)⁻¹ * t p u hu * s p u hu = t p u hu ^ 2 := by
  have h := congrArg (SemidirectProduct.inr (φ := action p u hu)) HostBS.relation
  simpa only [map_mul, map_inv, map_pow, t, s] using h

theorem a_tpow (n : ℕ) : (t p u hu ^ n)⁻¹ * a p u hu * t p u hu ^ n =
    SemidirectProduct.inl (lamp p n) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [pow_succ (t p u hu) n, mul_inv_rev]
    calc
      _ = (t p u hu)⁻¹ * ((t p u hu ^ n)⁻¹ * a p u hu * t p u hu ^ n) * t p u hu := by
        simp only [mul_assoc]
      _ = SemidirectProduct.inl (lamp p (n + 1)) := by rw [ih, lamp_t]
      _ = _ := by simp

theorem a_periodic : (t p u hu ^ (p ^ 2))⁻¹ * a p u hu * t p u hu ^ (p ^ 2) = a p u hu := by
  rw [a_tpow]
  simp [a]

theorem a_commutes_t [Fact (1 < p)] :
    Commute (a p u hu) ((t p u hu)⁻¹ * a p u hu * t p u hu) := by
  change Commute (SemidirectProduct.inl (lamp p 0))
    ((t p u hu)⁻¹ * SemidirectProduct.inl (lamp p 0) * t p u hu)
  rw [lamp_t, zero_add]
  apply Commute.map
  apply HostPartition.generators_commute
  simp

theorem semidirect_torsionFree {N G : Type*} [Group N] [Group G]
    [IsMulTorsionFree N] [IsMulTorsionFree G] (φ : G →* MulAut N) :
    IsMulTorsionFree (N ⋊[φ] G) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro x hx hf
  obtain ⟨n, hn, hp⟩ := hf.exists_pow_eq_one
  have hr : x.right ^ n = 1 := by
    have h := congrArg (SemidirectProduct.rightHom (φ := φ)) hp
    simpa only [map_pow, map_one, SemidirectProduct.rightHom_eq_right] using h
  have hr1 : x.right = 1 := (pow_eq_one_iff_left hn.ne').mp hr
  have heq : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext <;> simp [hr1]
  rw [heq, ← map_pow] at hp
  have hl : x.left ^ n = 1 := SemidirectProduct.inl_injective (hp.trans (map_one _).symm)
  have hl1 : x.left = 1 := (pow_eq_one_iff_left hn.ne').mp hl
  exact hx (by rw [heq, hl1, map_one])

theorem kernel_torsionFree [NeZero p] : IsMulTorsionFree (Kernel p) :=
  HostPartition.torsionFree (residue p)

theorem model_torsionFree [NeZero p] : IsMulTorsionFree (Model p u hu) := by
  let := kernel_torsionFree p
  let := HostBS.torsionFree
  exact semidirect_torsionFree _

open Word

def aWord : Word 3 := gen 0
def tWord : Word 3 := gen 1
def sWord : Word 3 := gen 2

def presentation : FP 3 4 where
  relator := Fin.cases (conjugate aWord sWord ++ inverse aWord)
    (Fin.cases (conjugate tWord sWord ++ inverse (power tWord 2))
      (Fin.cases (conjugate aWord (power tWord (p ^ 2)) ++ inverse aWord)
        (fun _ ↦ commutator aWord (conjugate aWord tWord))))

noncomputable def generators : Fin 3 → Model p u hu :=
  Fin.cases (a p u hu) (Fin.cases (t p u hu) (fun _ ↦ s p u hu))

@[simp] theorem eval_aWord : eval (generators p u hu) aWord = a p u hu := rfl
@[simp] theorem eval_tWord : eval (generators p u hu) tWord = t p u hu := rfl
@[simp] theorem eval_sWord : eval (generators p u hu) sWord = s p u hu := rfl

theorem generators_relator [Fact (1 < p)] (i : Fin 4) :
    eval (generators p u hu) ((presentation p).relator i) = 1 := by
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ Fin.cases ?_ (fun l ↦ ?_) k) j) i
  · change eval _ (conjugate aWord sWord ++ inverse aWord) = 1
    simp [a_s]
  · change eval _ (conjugate tWord sWord ++ inverse (power tWord 2)) = 1
    simp [t_s]
  · change eval _ (conjugate aWord (power tWord (p ^ 2)) ++ inverse aWord) = 1
    simp [a_periodic]
  · have hl : l = 0 := Fin.eq_zero l
    subst l
    simp only [presentation, Fin.cases_succ, eval_commutator, eval_conjugate, eval_aWord,
      eval_tWord]
    have h := a_commutes_t p u hu
    rw [h.inv_left.inv_right.eq]
    simp [mul_assoc]

noncomputable def toModel [Fact (1 < p)] : (presentation p).Group →* Model p u hu :=
  PresentedGroup.toGroup (f := generators p u hu) (by
    rintro _ ⟨i, rfl⟩
    exact generators_relator p u hu i)

@[simp] theorem toModel_of [Fact (1 < p)] (i : Fin 3) :
    toModel p u hu (PresentedGroup.of i) = generators p u hu i := PresentedGroup.toGroup.of _

end SmallPresentationStatements.Host
