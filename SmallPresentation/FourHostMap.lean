module

public import SmallPresentation.FourPacking

/-! The exact unsigned host maps onto the literal four-relator output. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral
open Word

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

noncomputable def hostToOutput : (Host.presentation p).Group →* (fourPresentation Q p).Group :=
  PresentedGroup.toGroup (f := ![FourPacking.outputA Q p, FourPacking.outputT Q p,
    FourPacking.outputS Q p]) (by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change Elimination.conjugate (FourPacking.outputA Q p) (FourPacking.outputS Q p) *
        (FourPacking.outputA Q p)⁻¹ = 1
      rw [FourPacking.output_a_s, mul_inv_cancel]
    · change Elimination.conjugate (FourPacking.outputT Q p) (FourPacking.outputS Q p) *
        (FourPacking.outputT Q p ^ 2)⁻¹ = 1
      rw [FourPacking.output_t_s, mul_inv_cancel]
    · change eval ![FourPacking.outputA Q p, FourPacking.outputT Q p, FourPacking.outputS Q p]
        (conjugate (gen 0) (power (gen 1) (p ^ 2)) ++ inverse (gen 0)) = 1
      simp only [eval_append, eval_conjugate, eval_power, eval_gen, eval_inverse,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      change Elimination.conjugate (FourPacking.outputA Q p)
        (FourPacking.outputT Q p ^ (p ^ 2)) * (FourPacking.outputA Q p)⁻¹ = 1
      rw [FourPacking.output_period, mul_inv_cancel]
    · change Elimination.commutator (FourPacking.outputA Q p)
        (Elimination.conjugate (FourPacking.outputA Q p) (FourPacking.outputT Q p)) = 1
      exact (PackingAlgebra.commutator_eq_one_iff _ _).mpr (FourPacking.output_seed Q p))

@[simp] theorem hostToOutput_a : hostToOutput Q p (Host.finiteA p) = FourPacking.outputA Q p :=
  PresentedGroup.toGroup.of _
@[simp] theorem hostToOutput_t : hostToOutput Q p (Host.finiteT p) = FourPacking.outputT Q p :=
  PresentedGroup.toGroup.of _
@[simp] theorem hostToOutput_s : hostToOutput Q p (Host.finiteS p) = FourPacking.outputS Q p :=
  PresentedGroup.toGroup.of _

@[simp] theorem hostToOutput_lamp (v : ZMod (p ^ 2)) :
    hostToOutput Q p (Host.finiteLamp p v) = FourPacking.outputLamp Q p v := by
  simp only [Host.finiteLamp, FourPacking.outputLamp, HostAlgebra.cyclicLamp,
    HostAlgebra.lamp, Elimination.conjugate, map_mul, map_inv, map_pow,
    hostToOutput_a, hostToOutput_t]

variable (hp : p.Prime) (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

noncomputable def hostModelToOutput : Host.Model p u hu →* (fourPresentation Q p).Group :=
  (hostToOutput Q p).comp (Host.fromModel p hp ho u hu)

@[simp] theorem hostModelToOutput_lamp (v : ZMod (p ^ 2)) :
    hostModelToOutput Q p hp ho u hu (SemidirectProduct.inl (Host.lamp p v)) =
      FourPacking.outputLamp Q p v := by
  simp only [hostModelToOutput, MonoidHom.comp_apply, Host.fromModel_lamp, hostToOutput_lamp]

@[simp] theorem hostModelToOutput_a :
    hostModelToOutput Q p hp ho u hu (Host.a p u hu) = FourPacking.outputA Q p := by
  simp only [hostModelToOutput, MonoidHom.comp_apply, Host.fromModel_a, hostToOutput_a]
@[simp] theorem hostModelToOutput_t :
    hostModelToOutput Q p hp ho u hu (Host.t p u hu) = FourPacking.outputT Q p := by
  simp only [hostModelToOutput, MonoidHom.comp_apply, Host.fromModel_t, hostToOutput_t]
@[simp] theorem hostModelToOutput_s :
    hostModelToOutput Q p hp ho u hu (Host.s p u hu) = FourPacking.outputS Q p := by
  simp only [hostModelToOutput, MonoidHom.comp_apply, Host.fromModel_s, hostToOutput_s]

theorem hostModelToOutput_base :
    (hostModelToOutput Q p hp ho u hu).comp SemidirectProduct.inl = FourPacking.baseMap Q p hp ho := by
  apply PresentedGroup.ext
  intro v
  change hostModelToOutput Q p hp ho u hu (SemidirectProduct.inl (Host.lamp p v)) =
    FourPacking.baseMap Q p hp ho (Host.lamp p v)
  rw [FourPacking.baseMap_lamp, hostModelToOutput_lamp]

end SmallPresentationStatements.FourCentral
