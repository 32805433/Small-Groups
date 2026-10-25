module

public import SmallPresentation.PackingBase
public import SmallPresentation.PackingReduction
public import SmallPresentation.HostArithmetic

/-! An explicit affine detector for the absorbed presentation. Its base is the
literal quotient by all signed rows, and its translation has the required finite period. -/
@[expose] public section

namespace SmallPresentationStatements.AbsorbedPacking

open Word
variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

abbrev Base := PackingBase.Group Q (Host.residue p)

def lamp (v : ZMod (p ^ 2)) : Base Q p := PackingBase.lamp Q (Host.residue p) v

def shift : MulAut (Base Q p) :=
  PackingBase.permAut Q (Host.residue p) (Host.shiftPerm p) (Host.shift_partition p)

variable (u : (ZMod (p ^ 2))ˣ)

def doubling : MulAut (Base Q p) :=
  PackingBase.permAut Q (Host.residue p) (Host.doublePerm p u) (Host.double_partition p u)

@[simp] theorem shift_lamp (v : ZMod (p ^ 2)) : shift Q p (lamp Q p v) = lamp Q p (v + 1) :=
  PackingBase.permAut_lamp _ _ _ _ _

@[simp] theorem shift_inv_lamp (v : ZMod (p ^ 2)) : (shift Q p)⁻¹ (lamp Q p v) = lamp Q p (v - 1) :=
  PackingBase.permAut_inv_lamp _ _ _ _ _

@[simp] theorem doubling_lamp (v : ZMod (p ^ 2)) :
    doubling Q p u (lamp Q p v) = lamp Q p (u * v) := PackingBase.permAut_lamp _ _ _ _ _

@[simp] theorem doubling_inv_lamp (v : ZMod (p ^ 2)) :
    (doubling Q p u)⁻¹ (lamp Q p v) = lamp Q p (u⁻¹ * v) :=
  PackingBase.permAut_inv_lamp _ _ _ _ _

theorem shift_pow_lamp (n : ℕ) (v : ZMod (p ^ 2)) :
    (shift Q p ^ n) (lamp Q p v) = lamp Q p (v + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (shift Q p), MulAut.mul_apply, ih, shift_lamp]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]

theorem shift_period : shift Q p ^ (p ^ 2) = 1 := by
  apply MulEquiv.toMonoidHom_injective
  apply PackingBase.hom_ext Q (Host.residue p)
  intro v
  change (shift Q p ^ (p ^ 2)) (lamp Q p v) = lamp Q p v
  simp [shift_pow_lamp]

variable (hu : (u : ZMod (p ^ 2)) = 2)

include hu in
theorem action_relation :
    ((doubling Q p u)⁻¹)⁻¹ * (shift Q p)⁻¹ * (doubling Q p u)⁻¹ = ((shift Q p)⁻¹) ^ 2 := by
  apply MulEquiv.toMonoidHom_injective
  apply PackingBase.hom_ext Q (Host.residue p)
  intro v
  change doubling Q p u ((shift Q p)⁻¹ ((doubling Q p u)⁻¹ (lamp Q p v))) =
    (shift Q p)⁻¹ ((shift Q p)⁻¹ (lamp Q p v))
  simp only [doubling_inv_lamp, shift_inv_lamp, doubling_lamp]
  congr 1
  rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one, hu]
  ring

abbrev Detector := Base Q p ⋊[MonoidHom.id (MulAut (Base Q p))] MulAut (Base Q p)

def baseInclusion : Base Q p →* Detector Q p := SemidirectProduct.inl

def a : Detector Q p := baseInclusion Q p (lamp Q p 0)
def t : Detector Q p := SemidirectProduct.inr (shift Q p)⁻¹
def s : Detector Q p := SemidirectProduct.inr (doubling Q p u)⁻¹

theorem lamp_t (v : ZMod (p ^ 2)) :
    (t Q p)⁻¹ * baseInclusion Q p (lamp Q p v) * t Q p =
      baseInclusion Q p (lamp Q p (v + 1)) := by
  simpa only [t, MonoidHom.id_apply, inv_inv, shift_lamp, map_inv, baseInclusion] using
    (SemidirectProduct.inl_aut_inv (φ := MonoidHom.id _) (shift Q p)⁻¹ (lamp Q p v)).symm

include hu in
theorem lamp_s (v : ZMod (p ^ 2)) :
    (s Q p u)⁻¹ * baseInclusion Q p (lamp Q p v) * s Q p u =
      baseInclusion Q p (lamp Q p (2 * v)) := by
  simpa only [s, MonoidHom.id_apply, inv_inv, doubling_lamp, hu, map_inv, baseInclusion] using
    (SemidirectProduct.inl_aut_inv (φ := MonoidHom.id _) (doubling Q p u)⁻¹ (lamp Q p v)).symm

include hu in
theorem a_s : (s Q p u)⁻¹ * a Q p * s Q p u = a Q p := by
  simpa only [a, mul_zero] using lamp_s Q p u hu 0

include hu in
theorem t_s : (s Q p u)⁻¹ * t Q p * s Q p u = t Q p ^ 2 := by
  have h := congrArg (SemidirectProduct.inr (φ := MonoidHom.id (MulAut (Base Q p))))
    (action_relation Q p u hu)
  simpa only [map_mul, map_inv, map_pow, t, s] using h

theorem t_period : t Q p ^ (p ^ 2) = 1 := by
  rw [t, ← map_pow, inv_pow, shift_period, inv_one, map_one]

theorem a_commutes_t [Fact (1 < p)] :
    Commute (a Q p) ((t Q p)⁻¹ * a Q p * t Q p) := by
  change Commute (baseInclusion Q p (lamp Q p 0))
    ((t Q p)⁻¹ * baseInclusion Q p (lamp Q p 0) * t Q p)
  rw [lamp_t, zero_add]
  apply Commute.map
  apply PackingBase.lamps_commute
  simp

include hu in
include hu in
theorem lamp_spow (n : ℕ) (v : ZMod (p ^ 2)) :
    (s Q p u ^ n)⁻¹ * baseInclusion Q p (lamp Q p v) * s Q p u ^ n =
      baseInclusion Q p (lamp Q p (2 ^ n * v)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (s Q p u), mul_inv_rev]
    calc
      _ = (s Q p u)⁻¹ * ((s Q p u ^ n)⁻¹ * baseInclusion Q p (lamp Q p v) *
          s Q p u ^ n) * s Q p u := by simp only [mul_assoc]
      _ = _ := by rw [ih, lamp_s Q p u hu]; simp only [pow_succ', mul_assoc]

def generators : Fin 2 → Detector Q p := ![a Q p * t Q p, s Q p u]

@[simp] theorem eval_s : eval (generators Q p u) (gen 1) = s Q p u := rfl

include hu in
@[simp] theorem eval_T : eval (generators Q p u) eliminatedT = t Q p := by
  change Elimination.recoveredT (a Q p * t Q p) (s Q p u) = t Q p
  exact Elimination.recover_t _ _ _ (a_s Q p u hu) (t_s Q p u hu)

include hu in
@[simp] theorem eval_A : eval (generators Q p u) eliminatedA = a Q p := by
  simp only [eliminatedA, eval_append, eval_gen, eval_inverse, eval_T Q p u hu]
  change (a Q p * t Q p) * (t Q p)⁻¹ = a Q p
  exact mul_inv_cancel_right _ _

include hu in
theorem eval_stored (n : ℕ) :
    eval (generators Q p u) (conjugate (conjugate eliminatedA eliminatedT) (power (gen 1) n)) =
      baseInclusion Q p (lamp Q p (2 ^ n)) := by
  simp only [eval_conjugate, eval_power, eval_s, eval_A Q p u hu, eval_T Q p u hu]
  change (s Q p u ^ n)⁻¹ * ((t Q p)⁻¹ * baseInclusion Q p (lamp Q p 0) * t Q p) * s Q p u ^ n = _
  rw [lamp_t, zero_add, lamp_spow Q p u hu, mul_one]

variable (hp3 : 3 ≤ p) (hL : L ≤ p - 1)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (ho₁ : orderOf (2 : ZMod p) = p - 1)

include hu hp3 hL ho ho₁ in
theorem eval_dyadic :
    eval (generators Q p u) (dyadicWord Q p eliminatedA eliminatedT (gen 1)) = 1 := by
  rw [dyadicWord, eval_flatten, List.map_ofFn]
  apply List.prod_eq_one
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  simp only [Function.comp_def, eval_subst_pair, eval_stored Q p u hu]
  have hrow := PackingBase.lamp_row Q (Host.residue p)
    ((2 : ZMod (p ^ 2)) ^ i.val) (2 ^ (i.val + p - 1))
    (by simpa only [map_pow, map_ofNat] using HostAlgebra.dyadic_pair_same_residue (by omega : 1 ≤ p) ho₁ i.val)
    (HostAlgebra.dyadic_pair_distinct hp3 hL ho i) i
  have hh := congrArg (baseInclusion Q p) hrow
  simp only [PackingBase.map_pair_eval, map_one] at hh
  exact hh

include hu hp3 hL ho ho₁ in
theorem generators_relator [Fact (1 < p)] (i : Fin 3) :
    eval (generators Q p u) ((threePresentation Q p).relator i) = 1 := by
  fin_cases i
  · change eval _ actionRow = 1
    simp only [actionRow, eval_append, eval_conjugate, eval_inverse, eval_power,
      eval_s, eval_T Q p u hu, t_s Q p u hu, mul_inv_cancel]
  · change eval _ commutationRow = 1
    simp only [commutationRow, eval_commutator, eval_conjugate,
      eval_A Q p u hu, eval_T Q p u hu]
    exact (PackingAlgebra.commutator_eq_one_iff _ _).mpr (a_commutes_t Q p)
  · change eval _ (power eliminatedT (p ^ 2) ++ inverse
        (dyadicWord Q p eliminatedA eliminatedT (gen 1))) = 1
    simp only [eval_append, eval_power, eval_T Q p u hu,
      t_period, eval_inverse, eval_dyadic Q p u hu hp3 hL ho ho₁, inv_one, mul_one]

noncomputable def detector [Fact (1 < p)] : (threePresentation Q p).Group →* Detector Q p :=
  PresentedGroup.toGroup (f := generators Q p u) (by
    rintro _ ⟨i,rfl⟩
    exact generators_relator Q p u hu hp3 hL ho ho₁ i)

@[simp] theorem detector_of [Fact (1 < p)] (j : Fin 2) :
    detector Q p u hu hp3 hL ho ho₁ (PresentedGroup.of j) = generators Q p u j :=
  PresentedGroup.toGroup.of _

def outputS : (threePresentation Q p).Group := PresentedGroup.of 1

def outputT : (threePresentation Q p).Group :=
  Elimination.recoveredT (PresentedGroup.of 0) (outputS Q p)

def outputA : (threePresentation Q p).Group :=
  Elimination.recoveredA (PresentedGroup.of 0) (outputS Q p)

@[simp] theorem output_eval_T :
    eval (PresentedGroup.of (rels := (threePresentation Q p).relSet)) eliminatedT = outputT Q p := rfl

@[simp] theorem output_eval_A :
    eval (PresentedGroup.of (rels := (threePresentation Q p).relSet)) eliminatedA = outputA Q p := by
  simp only [eliminatedA, eval_append, eval_gen, eval_inverse, output_eval_T]
  rfl

theorem output_t_s : Elimination.conjugate (outputT Q p) (outputS Q p) = outputT Q p ^ 2 := by
  have h := (threePresentation Q p).eval_relator 0
  change eval _ actionRow = 1 at h
  simp only [actionRow, eval_append, eval_conjugate, eval_inverse, eval_power, eval_gen,
    output_eval_T] at h
  exact mul_inv_eq_one.mp h

theorem output_a_s : Elimination.conjugate (outputA Q p) (outputS Q p) = outputA Q p :=
  Elimination.recoveredA_fixed _ _ (output_t_s Q p)

theorem output_seed : Commute (outputA Q p)
    (Elimination.conjugate (outputA Q p) (outputT Q p)) := by
  apply (PackingAlgebra.commutator_eq_one_iff _ _).mp
  have h := (threePresentation Q p).eval_relator 1
  change eval _ commutationRow = 1 at h
  simpa only [commutationRow, eval_commutator, eval_conjugate, output_eval_A, output_eval_T,
    Elimination.commutator, Elimination.conjugate] using h

theorem output_fused : outputT Q p ^ (p ^ 2) =
    eval (PresentedGroup.of (rels := (threePresentation Q p).relSet))
      (dyadicWord Q p eliminatedA eliminatedT (gen 1)) := by
  have h := (threePresentation Q p).eval_relator 2
  change eval _ (power eliminatedT (p ^ 2) ++ inverse
    (dyadicWord Q p eliminatedA eliminatedT (gen 1))) = 1 at h
  simp only [eval_append, eval_power, output_eval_T, eval_inverse] at h
  exact mul_inv_eq_one.mp h

theorem output_period : Elimination.conjugate (outputA Q p) (outputT Q p ^ (p ^ 2)) = outputA Q p := by
  have h := PackingAlgebra.derived_period Q p (p ^ 2) eliminatedA eliminatedT (gen 1)
    (PresentedGroup.of (rels := (threePresentation Q p).relSet))
    (by simpa only [output_eval_A, eval_gen, outputS] using output_a_s Q p)
    (by simpa only [output_eval_A, output_eval_T] using output_seed Q p)
    (by simpa only [output_eval_T] using output_fused Q p)
  simpa only [output_eval_A, output_eval_T] using h

def outputLamp (v : ZMod (p ^ 2)) : (threePresentation Q p).Group :=
  HostAlgebra.cyclicLamp (outputA Q p) (outputT Q p) v

variable (hp : p.Prime)

include hp ho in
theorem output_lamps_commute (v w : ZMod (p ^ 2)) (h : Host.residue p v ≠ Host.residue p w) :
    Commute (outputLamp Q p v) (outputLamp Q p w) :=
  HostAlgebra.cyclicLamp_commute (outputA Q p) (outputT Q p) (outputS Q p)
    (output_a_s Q p) (output_t_s Q p) (output_seed Q p) hp ho (output_period Q p) v w h

noncomputable def baseMap : Host.Kernel p →* (threePresentation Q p).Group :=
  PresentedGroup.toGroup (f := outputLamp Q p) (by
    rintro _ ⟨v,w,h,rfl⟩
    simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr (output_lamps_commute Q p ho hp v w h))

@[simp] theorem baseMap_lamp (v : ZMod (p ^ 2)) :
    baseMap Q p ho hp (Host.lamp p v) = outputLamp Q p v := PresentedGroup.toGroup.of _

theorem lamp_tpow (n : ℕ) (v : ZMod (p ^ 2)) :
    (t Q p ^ n)⁻¹ * baseInclusion Q p (lamp Q p v) * t Q p ^ n =
      baseInclusion Q p (lamp Q p (v + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (t Q p), mul_inv_rev]
    calc
      _ = (t Q p)⁻¹ * ((t Q p ^ n)⁻¹ * baseInclusion Q p (lamp Q p v) *
          t Q p ^ n) * t Q p := by simp only [mul_assoc]
      _ = _ := by rw [ih, lamp_t]; simp only [Nat.cast_add, Nat.cast_one, add_assoc]

include hu hp3 hL ho ho₁ in
theorem detector_outputA [Fact (1 < p)] :
    detector Q p u hu hp3 hL ho ho₁ (outputA Q p) = a Q p := by
  rw [← output_eval_A, map_eval]
  simpa only [detector_of] using eval_A Q p u hu

include hu hp3 hL ho ho₁ in
theorem detector_outputT [Fact (1 < p)] :
    detector Q p u hu hp3 hL ho ho₁ (outputT Q p) = t Q p := by
  rw [← output_eval_T, map_eval]
  simpa only [detector_of] using eval_T Q p u hu

include hu hp3 hL ho ho₁ in
theorem detector_outputLamp [Fact (1 < p)] [NeZero (p ^ 2)] (v : ZMod (p ^ 2)) :
    detector Q p u hu hp3 hL ho ho₁ (outputLamp Q p v) = baseInclusion Q p (lamp Q p v) := by
  simp only [outputLamp, HostAlgebra.cyclicLamp, HostAlgebra.lamp, Elimination.conjugate,
    map_mul, map_inv, map_pow, detector_outputA Q p u hu hp3 hL ho ho₁,
    detector_outputT Q p u hu hp3 hL ho ho₁]
  change (t Q p ^ v.val)⁻¹ * baseInclusion Q p (lamp Q p 0) * t Q p ^ v.val = _
  rw [lamp_tpow Q p, zero_add, ZMod.natCast_zmod_val]

include hu hp3 hL ho ho₁ hp in
theorem detector_baseMap [Fact (1 < p)] :
    (detector Q p u hu hp3 hL ho ho₁).comp (baseMap Q p ho hp) =
      (baseInclusion Q p).comp (PackingBase.quotient Q (Host.residue p)) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply PresentedGroup.ext
  intro v
  change detector Q p u hu hp3 hL ho ho₁ (baseMap Q p ho hp (Host.lamp p v)) = _
  rw [baseMap_lamp, detector_outputLamp Q p u hu hp3 hL ho ho₁]
  rfl

include hu hp3 hL ho ho₁ hp in
theorem upper_kernel [Fact (1 < p)] :
    (baseMap Q p ho hp).ker ≤ PackingBase.kernel Q (Host.residue p) := by
  rw [← PackingBase.quotient_ker]
  exact PackingReduction.upper_of_detector (baseMap Q p ho hp)
    (PackingBase.quotient Q (Host.residue p)) (detector Q p u hu hp3 hL ho ho₁)
    (baseInclusion Q p) SemidirectProduct.inl_injective
    (detector_baseMap Q p u hu hp3 hL ho ho₁ hp)

@[simp] theorem baseMap_row (v w : ZMod (p ^ 2)) (i : Fin L) :
    baseMap Q p ho hp (PackingBase.row Q (Host.residue p) v w i) =
      eval ![eval ![outputLamp Q p v,outputLamp Q p w] code₁,
        eval ![outputLamp Q p v,outputLamp Q p w] code₂] (Q.relator i) := by
  have h (z : ZMod (p ^ 2)) : baseMap Q p ho hp (HostPartition.generator (Host.residue p) z) =
      outputLamp Q p z := baseMap_lamp Q p ho hp z
  simp only [PackingBase.row, PackingBase.map_pair_eval, h]

theorem output_stored [NeZero (p ^ 2)] (n : ℕ) :
    eval (PresentedGroup.of (rels := (threePresentation Q p).relSet))
      (conjugate (conjugate eliminatedA eliminatedT) (power (gen 1) n)) =
      outputLamp Q p (2 ^ n) := by
  simp only [eval_conjugate, eval_power, eval_gen, output_eval_A, output_eval_T]
  change PackingAlgebra.storedLetter (outputA Q p) (outputT Q p) (outputS Q p) n = _
  rw [HostAlgebra.storedLetter_index _ _ _ (output_a_s Q p) (output_t_s Q p)]
  have h := HostAlgebra.cyclicLamp_natCast (outputA Q p) (outputT Q p) (p ^ 2)
    (output_period Q p) (2 ^ n)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, HostAlgebra.lamp, outputLamp] using h.symm

noncomputable def slot (i : Fin L) : (threePresentation Q p).Group :=
  baseMap Q p ho hp (PackingBase.row Q (Host.residue p) (2 ^ i.val) (2 ^ (i.val + p - 1)) i)

include hp in
theorem output_dyadic_slots :
    eval (PresentedGroup.of (rels := (threePresentation Q p).relSet))
      (dyadicWord Q p eliminatedA eliminatedT (gen 1)) = (List.ofFn (slot Q p ho hp)).prod := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  simp only [dyadicWord, eval_flatten, List.map_ofFn, Function.comp_def, eval_subst_pair,
    output_stored]
  congr 2
  funext i
  exact (baseMap_row Q p ho hp _ _ i).symm

include hp in
theorem output_slots_fused : (List.ofFn (slot Q p ho hp)).prod = outputT Q p ^ (p ^ 2) := by
  rw [← output_dyadic_slots Q p ho hp, ← output_fused Q p]

end SmallPresentationStatements.AbsorbedPacking
