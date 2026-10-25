module

public import SmallPresentation.AbsorbedPacking
public import SmallPresentation.SlotIsolation
public import SmallPresentation.PackingBaseProduct
public import SmallPresentation.HostFiber
public import SmallPresentation.HostInverse
public import SmallPresentation.SignedTietze

/-! The concrete maps and both kernel inclusions for the four-row output.
The embedding uses the proved generic relative small-cancellation theorem. -/
@[expose] public section

namespace SmallPresentationStatements.FourPacking

open Word
open scoped commutatorElement

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

theorem packed_eval {n : ℕ} {G : Type*} [Group G] (f : Fin n → G) (a t : Word n) :
    eval f (packedWord Q p a t) =
      (List.ofFn fun i : Fin L ↦ SlotIsolation.encodedValue Q i
        (HostAlgebra.lamp (eval f a) (eval f t) i.val)
        (HostAlgebra.lamp (eval f a) (eval f t) (p + i.val))).prod := by
  simp only [packedWord, eval_flatten, List.map_ofFn, Function.comp_def,
    eval_conjugate, eval_power, eval_subst_pair]
  congr 2
  funext i
  rw [← eval_subst_pair ![eval f a, (eval f t ^ p)⁻¹ * eval f a * eval f t ^ p]
    code₁ code₂ (Q.relator i)]
  change Elimination.conjugate (SlotIsolation.encodedValue Q i (eval f a)
    (HostAlgebra.lamp (eval f a) (eval f t) p)) ((eval f t) ^ i.val) = _
  rw [SlotIsolation.encodedValue_conjugate, ← HostAlgebra.lamp_add]
  rfl

theorem slot_pair (hp : p.Prime) (i : Fin L) :
    (i.val : ZMod (p ^ 2)) ≠ ((p + i.val : ℕ) : ZMod (p ^ 2)) ∧
      Host.residue p i.val = Host.residue p ((p + i.val : ℕ) : ZMod (p ^ 2)) := by
  constructor
  · intro h
    have hz : (p : ZMod (p ^ 2)) = 0 := by
      have h' : (p : ZMod (p ^ 2)) + i.val = 0 + i.val := by
        simpa only [Nat.cast_add, zero_add] using h.symm
      exact add_right_cancel h'
    have hd := (ZMod.natCast_eq_zero_iff p (p ^ 2)).mp hz
    have hlt : p < p ^ 2 := by
      have h := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
      simpa only [Nat.mul_one, pow_two] using h
    exact Nat.not_dvd_of_pos_of_lt hp.pos hlt hd
  · simp

theorem slot_injective (hL : L ≤ p) :
    Function.Injective (fun i : Fin L ↦ Host.residue p (i.val : ZMod (p ^ 2))) := by
  intro i j h
  apply Fin.ext
  have h' : (i.val : ZMod p) = (j.val : ZMod p) := by simpa only [map_natCast] using h
  have hm := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp h'
  simpa only [Nat.mod_eq_of_lt (lt_of_lt_of_le i.isLt hL),
    Nat.mod_eq_of_lt (lt_of_lt_of_le j.isLt hL)] using hm

variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)
variable (hp : p.Prime)

include hu hp in
theorem eval_packed :
    eval (AbsorbedPacking.generators Q p u) (packedWord Q p eliminatedA eliminatedT) = 1 := by
  rw [packed_eval]
  simp only [AbsorbedPacking.eval_A Q p u hu, AbsorbedPacking.eval_T Q p u hu]
  apply List.prod_eq_one
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  have hlamp (m : ℕ) : HostAlgebra.lamp (AbsorbedPacking.a Q p) (AbsorbedPacking.t Q p) m =
      AbsorbedPacking.baseInclusion Q p (AbsorbedPacking.lamp Q p m) := by
    change (AbsorbedPacking.t Q p ^ m)⁻¹ *
      AbsorbedPacking.baseInclusion Q p (AbsorbedPacking.lamp Q p 0) *
        AbsorbedPacking.t Q p ^ m = _
    simpa only [zero_add] using AbsorbedPacking.lamp_tpow Q p m 0
  rw [hlamp, hlamp]
  have hrow := PackingBase.lamp_row Q (Host.residue p)
    (i.val : ZMod (p ^ 2)) ((p + i.val : ℕ) : ZMod (p ^ 2))
    (slot_pair p hp i).2 (slot_pair p hp i).1 i
  have hh := congrArg (AbsorbedPacking.baseInclusion Q p) hrow
  simpa only [SlotIsolation.encodedValue, eval_subst_pair, PackingBase.map_pair_eval,
    map_one, AbsorbedPacking.lamp] using hh

include hu hp in
theorem generators_relator [Fact (1 < p)] (i : Fin 4) :
    eval (AbsorbedPacking.generators Q p u) ((fourPresentation Q p).relator i) = 1 := by
  fin_cases i
  · change eval _ actionRow = 1
    simp only [actionRow, eval_append, eval_conjugate, eval_inverse, eval_power,
      AbsorbedPacking.eval_s, AbsorbedPacking.eval_T Q p u hu,
      AbsorbedPacking.t_s Q p u hu, mul_inv_cancel]
  · change eval _ (conjugate eliminatedA (power eliminatedT (p ^ 2)) ++ inverse eliminatedA) = 1
    simp only [eval_append, eval_conjugate, eval_inverse, eval_power,
      AbsorbedPacking.eval_A Q p u hu, AbsorbedPacking.eval_T Q p u hu,
      AbsorbedPacking.t_period, inv_one, one_mul, mul_one, mul_inv_cancel]
  · change eval _ commutationRow = 1
    simp only [commutationRow, eval_commutator, eval_conjugate,
      AbsorbedPacking.eval_A Q p u hu, AbsorbedPacking.eval_T Q p u hu]
    exact (PackingAlgebra.commutator_eq_one_iff _ _).mpr (AbsorbedPacking.a_commutes_t Q p)
  · exact eval_packed Q p u hu hp

noncomputable def detector [Fact (1 < p)] : (fourPresentation Q p).Group →* AbsorbedPacking.Detector Q p :=
  PresentedGroup.toGroup (f := AbsorbedPacking.generators Q p u) (by
    rintro _ ⟨i, rfl⟩
    exact generators_relator Q p u hu hp i)

@[simp] theorem detector_of [Fact (1 < p)] (j : Fin 2) :
    detector Q p u hu hp (PresentedGroup.of j) = AbsorbedPacking.generators Q p u j :=
  PresentedGroup.toGroup.of _

def outputS : (fourPresentation Q p).Group := PresentedGroup.of 1
def outputT : (fourPresentation Q p).Group := Elimination.recoveredT (PresentedGroup.of 0) (outputS Q p)
def outputA : (fourPresentation Q p).Group := Elimination.recoveredA (PresentedGroup.of 0) (outputS Q p)

@[simp] theorem output_eval_T :
    eval (PresentedGroup.of (rels := (fourPresentation Q p).relSet)) eliminatedT = outputT Q p := rfl

@[simp] theorem output_eval_A :
    eval (PresentedGroup.of (rels := (fourPresentation Q p).relSet)) eliminatedA = outputA Q p := by
  simp only [eliminatedA, eval_append, eval_gen, eval_inverse, output_eval_T]
  rfl

theorem output_t_s : Elimination.conjugate (outputT Q p) (outputS Q p) = outputT Q p ^ 2 := by
  have h := (fourPresentation Q p).eval_relator 0
  change eval _ actionRow = 1 at h
  simp only [actionRow, eval_append, eval_conjugate, eval_inverse, eval_power, eval_gen,
    output_eval_T] at h
  exact mul_inv_eq_one.mp h

theorem output_a_s : Elimination.conjugate (outputA Q p) (outputS Q p) = outputA Q p :=
  Elimination.recoveredA_fixed _ _ (output_t_s Q p)

theorem output_period : Elimination.conjugate (outputA Q p) (outputT Q p ^ (p ^ 2)) = outputA Q p := by
  have h := (fourPresentation Q p).eval_relator 1
  change eval _ (conjugate eliminatedA (power eliminatedT (p ^ 2)) ++ inverse eliminatedA) = 1 at h
  simp only [eval_append, eval_conjugate, eval_inverse, eval_power, output_eval_A, output_eval_T] at h
  exact mul_inv_eq_one.mp h

theorem output_seed : Commute (outputA Q p) (Elimination.conjugate (outputA Q p) (outputT Q p)) := by
  apply (PackingAlgebra.commutator_eq_one_iff _ _).mp
  have h := (fourPresentation Q p).eval_relator 2
  change eval _ commutationRow = 1 at h
  simpa only [commutationRow, eval_commutator, eval_conjugate, output_eval_A, output_eval_T,
    Elimination.commutator, Elimination.conjugate] using h

theorem output_packed : eval (PresentedGroup.of (rels := (fourPresentation Q p).relSet))
    (packedWord Q p eliminatedA eliminatedT) = 1 := (fourPresentation Q p).eval_relator 3

def outputLamp (v : ZMod (p ^ 2)) : (fourPresentation Q p).Group :=
  HostAlgebra.cyclicLamp (outputA Q p) (outputT Q p) v

variable (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))

include hp ho in
theorem output_lamps_commute (v w : ZMod (p ^ 2)) (h : Host.residue p v ≠ Host.residue p w) :
    Commute (outputLamp Q p v) (outputLamp Q p w) :=
  HostAlgebra.cyclicLamp_commute (outputA Q p) (outputT Q p) (outputS Q p)
    (output_a_s Q p) (output_t_s Q p) (output_seed Q p) hp ho (output_period Q p) v w h

noncomputable def baseMap : Host.Kernel p →* (fourPresentation Q p).Group :=
  PresentedGroup.toGroup (f := outputLamp Q p) (by
    rintro _ ⟨v, w, h, rfl⟩
    simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr (output_lamps_commute Q p hp ho v w h))

@[simp] theorem baseMap_lamp (v : ZMod (p ^ 2)) :
    baseMap Q p hp ho (Host.lamp p v) = outputLamp Q p v := PresentedGroup.toGroup.of _

include hu hp in
theorem detector_outputA [Fact (1 < p)] :
    detector Q p u hu hp (outputA Q p) = AbsorbedPacking.a Q p := by
  rw [← output_eval_A, map_eval]
  simpa only [detector_of] using AbsorbedPacking.eval_A Q p u hu

include hu hp in
theorem detector_outputT [Fact (1 < p)] :
    detector Q p u hu hp (outputT Q p) = AbsorbedPacking.t Q p := by
  rw [← output_eval_T, map_eval]
  simpa only [detector_of] using AbsorbedPacking.eval_T Q p u hu

include hu hp in
theorem detector_outputLamp [Fact (1 < p)] [NeZero (p ^ 2)] (v : ZMod (p ^ 2)) :
    detector Q p u hu hp (outputLamp Q p v) =
      AbsorbedPacking.baseInclusion Q p (AbsorbedPacking.lamp Q p v) := by
  simp only [outputLamp, HostAlgebra.cyclicLamp, HostAlgebra.lamp, Elimination.conjugate,
    map_mul, map_inv, map_pow, detector_outputA Q p u hu hp, detector_outputT Q p u hu hp]
  change (AbsorbedPacking.t Q p ^ v.val)⁻¹ *
    AbsorbedPacking.baseInclusion Q p (AbsorbedPacking.lamp Q p 0) * AbsorbedPacking.t Q p ^ v.val = _
  rw [AbsorbedPacking.lamp_tpow, zero_add, ZMod.natCast_zmod_val]

include hu hp ho in
theorem detector_baseMap [Fact (1 < p)] :
    (detector Q p u hu hp).comp (baseMap Q p hp ho) =
      (AbsorbedPacking.baseInclusion Q p).comp (PackingBase.quotient Q (Host.residue p)) := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  apply PresentedGroup.ext
  intro v
  change detector Q p u hu hp (baseMap Q p hp ho (Host.lamp p v)) = _
  rw [baseMap_lamp, detector_outputLamp Q p u hu hp]
  rfl

include hu hp ho in
theorem upper_kernel [Fact (1 < p)] :
    (baseMap Q p hp ho).ker ≤ PackingBase.kernel Q (Host.residue p) := by
  rw [← PackingBase.quotient_ker]
  exact PackingReduction.upper_of_detector (baseMap Q p hp ho)
    (PackingBase.quotient Q (Host.residue p)) (detector Q p u hu hp)
    (AbsorbedPacking.baseInclusion Q p) SemidirectProduct.inl_injective
    (detector_baseMap Q p u hu hp ho)

@[simp] theorem baseMap_row (v w : ZMod (p ^ 2)) (i : Fin L) :
    baseMap Q p hp ho (PackingBase.row Q (Host.residue p) v w i) =
      SlotIsolation.encodedValue Q i (outputLamp Q p v) (outputLamp Q p w) := by
  have h (z : ZMod (p ^ 2)) : baseMap Q p hp ho (HostPartition.generator (Host.residue p) z) =
      outputLamp Q p z := baseMap_lamp Q p hp ho z
  simp only [PackingBase.row, PackingBase.map_pair_eval, h, SlotIsolation.encodedValue, eval_subst_pair]

include hp in
theorem output_storedProduct :
    SlotIsolation.storedProduct Q (outputLamp Q p)
      (fun i : Fin L ↦ i.val) (fun i ↦ ((p + i.val : ℕ) : ZMod (p ^ 2))) = 1 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have h := output_packed Q p
  rw [packed_eval] at h
  simpa only [output_eval_A, output_eval_T, SlotIsolation.storedProduct, outputLamp,
    HostAlgebra.cyclicLamp_natCast _ _ _ (output_period Q p)] using h

variable (hL : L ≤ p)

include hp ho hL in
theorem output_row_commutes_lamps (v w z : ZMod (p ^ 2))
    (hres : Host.residue p v = Host.residue p w) (hne : v ≠ w) (i : Fin L) :
    Commute (baseMap Q p hp ho (PackingBase.row Q (Host.residue p) v w i)) (outputLamp Q p z) := by
  rw [baseMap_row]
  apply SlotIsolation.row_commutes_all_lamps Q (outputA Q p) (outputT Q p) (outputS Q p)
    (output_a_s Q p) (output_t_s Q p) (output_seed Q p) hp ho (output_period Q p)
    (fun i : Fin L ↦ i.val) (fun i ↦ ((p + i.val : ℕ) : ZMod (p ^ 2)))
  · exact slot_pair p hp
  · exact slot_injective p hL
  · intro j
    change Commute (SlotIsolation.storedProduct Q (outputLamp Q p) _ _) (outputLamp Q p j)
    rw [output_storedProduct Q p hp]
    exact Commute.one_left _
  · exact hne
  · exact hres

include hp ho hL in
theorem lower_kernel :
    ⁅PackingBase.kernel Q (Host.residue p), (⊤ : Subgroup (Host.Kernel p))⁆ ≤
      (baseMap Q p hp ho).ker := by
  have hrows (r : Host.Kernel p) (hr : r ∈ PackingBase.rows Q (Host.residue p)) (x : Host.Kernel p) :
      Commute (baseMap Q p hp ho r) (baseMap Q p hp ho x) := by
    apply PackingReduction.commute_all_of_generators (baseMap Q p hp ho)
      (Set.range (Host.lamp p)) (PresentedGroup.closure_range_of _) _ _ x
    rintro _ ⟨z, rfl⟩
    rcases hr with ⟨v, w, hres, hne, i, rfl⟩
    rw [baseMap_lamp]
    exact output_row_commutes_lamps Q p hp ho hL v w z hres hne i
  have hcenter : ∀ r ∈ PackingBase.rows Q (Host.residue p),
      (baseMap Q p hp ho).rangeRestrict r ∈ Subgroup.center (baseMap Q p hp ho).range := by
    intro r hr
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, hx⟩ := y.property
    apply Subtype.ext
    change y.val * baseMap Q p hp ho r = baseMap Q p hp ho r * y.val
    rw [← hx]
    exact (hrows r hr x).symm
  have h := PackingKernel.commutator_normalClosure_le_kernel
    (baseMap Q p hp ho).rangeRestrict (PackingBase.rows Q (Host.residue p)) hcenter
  simpa only [MonoidHom.ker_rangeRestrict, PackingBase.kernel] using h

include hp ho hL in
theorem exists_embedding (hC : CentrallyClosed Q.Group) (hN : Noncyclic Q.Group) :
    ∃ f : Q.Group →* (fourPresentation Q p).Group, Function.Injective f := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  let u := Host.primitiveUnit p hp ho
  have hu : (u : ZMod (p ^ 2)) = 2 := Host.primitiveUnit_coe p hp ho
  let e := Host.fiberEquiv p (0 : ZMod p)
  let v : Fin p := ⟨0, hp.pos⟩
  let w : Fin p := ⟨1, hp.one_lt⟩
  have hvw : v ≠ w := by
    intro h
    have hh := congrArg Fin.val h
    change (0 : ℕ) = 1 at hh
    omega
  let j := PackingBaseProduct.sourceHom Q (Host.residue p) 0 e v w hvw
  have hj : Function.Injective j := PackingBaseProduct.sourceHom_injective Q
    (Host.residue p) 0 e v w hvw (SignedCoding.Relative.sourceHom_injective Q hN v w hvw)
  apply KernelSandwich.embedding_of_sandwich hC (baseMap Q p hp ho)
    (PackingBase.quotient Q (Host.residue p)) (PackingBase.quotient_surjective Q (Host.residue p))
    _ _ j hj
  · rw [PackingBase.quotient_ker]
    exact upper_kernel Q p u hu hp ho
  · rw [PackingBase.quotient_ker]
    exact lower_kernel Q p hp ho hL

include hp in
theorem base_torsionFree (hN : Noncyclic Q.Group) (hT : IsMulTorsionFree Q.Group) :
    IsMulTorsionFree (PackingBase.Group Q (Host.residue p)) := by
  classical
  let : NeZero p := ⟨hp.ne_zero⟩
  let : IsMulTorsionFree (SignedCoding.CodedGroup Q p) :=
    SignedCoding.Relative.codedGroup_torsionfree Q hN hT
  let : ∀ c : ZMod p, IsMulTorsionFree (PackingBaseProduct.FiberGroup Q (Host.residue p) c) :=
    fun c ↦ (PackingBaseProduct.fiberCodeEquiv Q (Host.residue p) c
      (Host.fiberEquiv p c)).injective.isMulTorsionFree
        (PackingBaseProduct.fiberCodeEquiv Q (Host.residue p) c
        (Host.fiberEquiv p c)).toMonoidHom
  exact (PackingBaseProduct.productEquiv Q (Host.residue p)).injective.isMulTorsionFree
    (PackingBaseProduct.productEquiv Q (Host.residue p)).toMonoidHom

end SmallPresentationStatements.FourPacking
