module

public import SmallPresentation.HostModel
public import SmallPresentation.HostArithmetic

/-! The inverse from the exact host semidirect product to its four-relator
presentation, using the primitive-root propagation of cross-factor commutations. -/
@[expose] public section

namespace SmallPresentationStatements.Host

open Word
open scoped commutatorElement

variable (p : ℕ)

noncomputable def finiteA : (presentation p).Group := PresentedGroup.of 0
noncomputable def finiteT : (presentation p).Group := PresentedGroup.of 1
noncomputable def finiteS : (presentation p).Group := PresentedGroup.of 2

theorem finite_a_s : (finiteS p)⁻¹ * finiteA p * finiteS p = finiteA p := by
  have h := (presentation p).eval_relator 0
  change ((finiteS p)⁻¹ * finiteA p * finiteS p) * (finiteA p)⁻¹ = 1 at h
  exact mul_inv_eq_one.mp h

theorem finite_t_s : (finiteS p)⁻¹ * finiteT p * finiteS p = finiteT p ^ 2 := by
  have h := (presentation p).eval_relator 1
  change ((finiteS p)⁻¹ * finiteT p * finiteS p) * (finiteT p ^ 2)⁻¹ = 1 at h
  exact mul_inv_eq_one.mp h

theorem finite_periodic : (finiteT p ^ (p ^ 2))⁻¹ * finiteA p * finiteT p ^ (p ^ 2) = finiteA p := by
  have h := (presentation p).eval_relator 2
  change eval (PresentedGroup.of (rels := (presentation p).relSet))
    (conjugate aWord (power tWord (p ^ 2)) ++ inverse aWord) = 1 at h
  simp only [eval_append, eval_conjugate, eval_power, eval_inverse, aWord, tWord, eval_gen] at h
  exact mul_inv_eq_one.mp h

theorem finite_seed : Commute (finiteA p) ((finiteT p)⁻¹ * finiteA p * finiteT p) := by
  have h := (presentation p).eval_relator 3
  change ⁅(finiteA p)⁻¹, ((finiteT p)⁻¹ * finiteA p * finiteT p)⁻¹⁆ = 1 at h
  exact Commute.inv_inv_iff.mp (commutatorElement_eq_one_iff_commute.mp h)

noncomputable def finiteLamp (v : ZMod (p ^ 2)) : (presentation p).Group :=
  HostAlgebra.cyclicLamp (finiteA p) (finiteT p) v

variable (hp : p.Prime) (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))

include hp ho in
theorem finite_lamps_commute (v w : ZMod (p ^ 2)) (h : residue p v ≠ residue p w) :
    Commute (finiteLamp p v) (finiteLamp p w) :=
  HostAlgebra.cyclicLamp_commute (finiteA p) (finiteT p) (finiteS p)
    (finite_a_s p) (finite_t_s p) (finite_seed p) hp ho (finite_periodic p) v w h

noncomputable def finiteKernel : Kernel p →* (presentation p).Group :=
  PresentedGroup.toGroup (f := finiteLamp p) (by
    rintro _ ⟨v, w, hvw, rfl⟩
    simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr (finite_lamps_commute p hp ho v w hvw))

@[simp] theorem finiteKernel_lamp (v : ZMod (p ^ 2)) :
    finiteKernel p hp ho (lamp p v) = finiteLamp p v := PresentedGroup.toGroup.of _

noncomputable def finiteBS : HostBS.Group →* (presentation p).Group :=
  HostBS.lift (finiteT p) (finiteS p) (finite_t_s p)

@[simp] theorem finiteBS_t : finiteBS p HostBS.t = finiteT p := HostBS.lift_t _ _ _
@[simp] theorem finiteBS_s : finiteBS p HostBS.s = finiteS p := HostBS.lift_s _ _ _

variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

theorem finite_shift_compatible :
    (finiteKernel p hp ho).comp (action p u hu HostBS.t).toMonoidHom =
      (MulAut.conj (finiteBS p HostBS.t)).toMonoidHom.comp (finiteKernel p hp ho) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply PresentedGroup.ext
  intro v
  change finiteKernel p hp ho ((action p u hu HostBS.t) (lamp p v)) =
    finiteBS p HostBS.t * finiteKernel p hp ho (lamp p v) * (finiteBS p HostBS.t)⁻¹
  simp only [action_t, shift_inv_lamp, finiteKernel_lamp, finiteBS_t]
  have h := HostAlgebra.cyclicLamp_shift (finiteA p) (finiteT p) (p ^ 2)
    (finite_periodic p) (v - 1)
  simp only [sub_add_cancel] at h
  have h' := congrArg (fun z ↦ finiteT p * z * (finiteT p)⁻¹) h
  simpa only [finiteLamp, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h'.symm

theorem finite_double_compatible :
    (finiteKernel p hp ho).comp (action p u hu HostBS.s).toMonoidHom =
      (MulAut.conj (finiteBS p HostBS.s)).toMonoidHom.comp (finiteKernel p hp ho) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply PresentedGroup.ext
  intro v
  change finiteKernel p hp ho ((action p u hu HostBS.s) (lamp p v)) =
    finiteBS p HostBS.s * finiteKernel p hp ho (lamp p v) * (finiteBS p HostBS.s)⁻¹
  simp only [action_s, doubling_inv_lamp, finiteKernel_lamp, finiteBS_s]
  have h := HostAlgebra.cyclicLamp_double (finiteA p) (finiteT p) (finiteS p) (p ^ 2)
    (finite_a_s p) (finite_t_s p) (finite_periodic p) ((u⁻¹ : (ZMod (p ^ 2))ˣ) * v)
  rw [← hu, ← mul_assoc, Units.mul_inv, one_mul] at h
  have h' := congrArg (fun z ↦ finiteS p * z * (finiteS p)⁻¹) h
  simpa only [finiteLamp, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using h'.symm

def compatibilitySubgroup {N G H : Type*} [Group N] [Group G] [Group H]
    (f : N →* H) (g : G →* H) (φ : G →* MulAut N) : Subgroup G where
  carrier := {z | ∀ x, f (φ z x) = g z * f x * (g z)⁻¹}
  one_mem' := by
    change ∀ x, f (φ 1 x) = g 1 * f x * (g 1)⁻¹
    simp
  mul_mem' := by
    intro a b ha hb
    change ∀ x, f (φ a x) = g a * f x * (g a)⁻¹ at ha
    change ∀ x, f (φ b x) = g b * f x * (g b)⁻¹ at hb
    intro x
    simp only [map_mul, MulAut.mul_apply, ha, hb, mul_inv_rev]
    simp only [mul_assoc]
  inv_mem' := by
    intro a ha
    change ∀ x, f (φ a x) = g a * f x * (g a)⁻¹ at ha
    intro x
    have h := congrArg (fun z ↦ (g a)⁻¹ * z * g a) (ha ((φ a)⁻¹ x))
    simpa only [map_inv, MulAut.apply_inv_self, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.symm

theorem finite_compatible (g : HostBS.Group) :
    (finiteKernel p hp ho).comp (action p u hu g).toMonoidHom =
      (MulAut.conj (finiteBS p g)).toMonoidHom.comp (finiteKernel p hp ho) := by
  have h : g ∈ compatibilitySubgroup (finiteKernel p hp ho) (finiteBS p) (action p u hu) := by
    apply HostBS.generated_by
    · exact fun x ↦ DFunLike.congr_fun (finite_shift_compatible p hp ho u hu) x
    · exact fun x ↦ DFunLike.congr_fun (finite_double_compatible p hp ho u hu) x
  exact MonoidHom.ext h

noncomputable def fromModel : Model p u hu →* (presentation p).Group :=
  SemidirectProduct.lift (finiteKernel p hp ho) (finiteBS p) (finite_compatible p hp ho u hu)

@[simp] theorem fromModel_lamp (v : ZMod (p ^ 2)) :
    fromModel p hp ho u hu (SemidirectProduct.inl (lamp p v)) = finiteLamp p v := by
  simp [fromModel]

@[simp] theorem fromModel_a : fromModel p hp ho u hu (a p u hu) = finiteA p := by
  simp [a, finiteLamp, HostAlgebra.cyclicLamp, HostAlgebra.lamp, Elimination.conjugate]

@[simp] theorem fromModel_t : fromModel p hp ho u hu (t p u hu) = finiteT p := by
  simp [fromModel, t]

@[simp] theorem fromModel_s : fromModel p hp ho u hu (s p u hu) = finiteS p := by
  simp [fromModel, s]

theorem fromModel_toModel [Fact (1 < p)] :
    (fromModel p hp ho u hu).comp (toModel p u hu) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · change fromModel p hp ho u hu (toModel p u hu (PresentedGroup.of 0)) = finiteA p
    rw [toModel_of]
    exact fromModel_a p hp ho u hu
  · change fromModel p hp ho u hu (toModel p u hu (PresentedGroup.of 1)) = finiteT p
    rw [toModel_of]
    exact fromModel_t p hp ho u hu
  · have hk : k = 0 := Fin.eq_zero k
    subst k
    change fromModel p hp ho u hu (toModel p u hu (PresentedGroup.of 2)) = finiteS p
    rw [toModel_of]
    exact fromModel_s p hp ho u hu

@[simp] theorem toModel_finiteA [Fact (1 < p)] :
    toModel p u hu (finiteA p) = a p u hu := toModel_of p u hu 0

@[simp] theorem toModel_finiteT [Fact (1 < p)] :
    toModel p u hu (finiteT p) = t p u hu := toModel_of p u hu 1

@[simp] theorem toModel_finiteS [Fact (1 < p)] :
    toModel p u hu (finiteS p) = s p u hu := toModel_of p u hu 2

@[simp] theorem toModel_finiteLamp [Fact (1 < p)] (v : ZMod (p ^ 2)) :
    toModel p u hu (finiteLamp p v) = SemidirectProduct.inl (lamp p v) := by
  simp only [finiteLamp, HostAlgebra.cyclicLamp, HostAlgebra.lamp, Elimination.conjugate,
    map_mul, map_inv, map_pow, toModel_finiteA, toModel_finiteT, a_tpow,
    ZMod.natCast_zmod_val]

theorem toModel_finiteKernel [Fact (1 < p)] :
    (toModel p u hu).comp (finiteKernel p hp ho) = SemidirectProduct.inl := by
  apply PresentedGroup.ext
  intro v
  change toModel p u hu (finiteKernel p hp ho (lamp p v)) = SemidirectProduct.inl (lamp p v)
  simp

theorem toModel_finiteBS [Fact (1 < p)] :
    (toModel p u hu).comp (finiteBS p) = SemidirectProduct.inr := by
  apply HostBS.hom_ext
  · simp [t]
  · simp [s]

theorem toModel_fromModel [Fact (1 < p)] :
    (toModel p u hu).comp (fromModel p hp ho u hu) = MonoidHom.id _ := by
  apply SemidirectProduct.hom_ext
  · apply MonoidHom.ext
    intro x
    change toModel p u hu (fromModel p hp ho u hu (SemidirectProduct.inl x)) =
      SemidirectProduct.inl x
    rw [fromModel, SemidirectProduct.lift_inl]
    exact DFunLike.congr_fun (toModel_finiteKernel p hp ho u hu) x
  · apply MonoidHom.ext
    intro x
    change toModel p u hu (fromModel p hp ho u hu (SemidirectProduct.inr x)) =
      SemidirectProduct.inr x
    rw [fromModel, SemidirectProduct.lift_inr]
    exact DFunLike.congr_fun (toModel_finiteBS p u hu) x

/-- The exact unsigned host presentation is the specified semidirect product.
Its normal subgroup is the direct product of the free groups on residue fibers. -/
noncomputable def presentationEquiv [Fact (1 < p)] : (presentation p).Group ≃* Model p u hu where
  toFun := toModel p u hu
  invFun := fromModel p hp ho u hu
  left_inv x := DFunLike.congr_fun (fromModel_toModel p hp ho u hu) x
  right_inv x := DFunLike.congr_fun (toModel_fromModel p hp ho u hu) x
  map_mul' := (toModel p u hu).map_mul

noncomputable def primitiveUnit : (ZMod (p ^ 2))ˣ :=
  (orderOf_pos_iff.mp (show 0 < orderOf (2 : ZMod (p ^ 2)) by
    rw [ho]
    exact Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt))).unit

theorem primitiveUnit_coe : (primitiveUnit p hp ho : ZMod (p ^ 2)) = 2 := rfl

include hp ho in
theorem presentation_torsionFree : IsMulTorsionFree (presentation p).Group := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  let u := primitiveUnit p hp ho
  have hu : (u : ZMod (p ^ 2)) = 2 := primitiveUnit_coe p hp ho
  let := model_torsionFree p u hu
  exact (presentationEquiv p hp ho u hu).injective.isMulTorsionFree
    (presentationEquiv p hp ho u hu).toMonoidHom

end SmallPresentationStatements.Host
