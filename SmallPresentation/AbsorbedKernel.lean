module

public import SmallPresentation.AbsorbedPacking
public import SmallPresentation.SlotIsolation
public import SmallPresentation.PackingBaseProduct
public import SmallPresentation.HostFiber

/-! The concrete lower half of the absorbed packing kernel sandwich. -/
@[expose] public section

namespace SmallPresentationStatements.AbsorbedPacking

open Word
open scoped commutatorElement

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

/-- The literal signed row is the value used by affine slot isolation. -/
theorem baseMap_row_encoded (hp : p.Prime)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (v w : ZMod (p ^ 2)) (i : Fin L) :
    baseMap Q p ho hp (PackingBase.row Q (Host.residue p) v w i) =
      SlotIsolation.encodedValue Q i (outputLamp Q p v) (outputLamp Q p w) := by
  rw [baseMap_row]
  simp only [SlotIsolation.encodedValue, eval_subst_pair]

theorem output_storedProduct (hp : p.Prime)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1)) :
    SlotIsolation.storedProduct Q (outputLamp Q p)
      (fun i : Fin L ↦ 2 ^ i.val) (fun i ↦ 2 ^ (i.val + p - 1)) = outputT Q p ^ (p ^ 2) := by
  rw [← output_slots_fused Q p ho hp]
  unfold SlotIsolation.storedProduct
  congr 2
  funext i
  exact (baseMap_row_encoded Q p hp ho _ _ i).symm

theorem output_period_commutes_lamps (j : ZMod (p ^ 2)) :
    Commute (outputT Q p ^ (p ^ 2)) (outputLamp Q p j) := by
  have ha : Commute (outputT Q p ^ (p ^ 2)) (outputA Q p) :=
    ((PackingAlgebra.fixed_iff_commute _ _).mp (output_period Q p)).symm
  have ht := Commute.pow_pow_self (outputT Q p) (p ^ 2) j.val
  exact (ht.inv_right.mul_right ha).mul_right ht

variable (hp : p.Prime) (hp3 : 3 ≤ p) (hL : L ≤ p - 1)
    (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (ho₁ : orderOf (2 : ZMod p) = p - 1)

include hp hp3 hL ho ho₁ in
theorem output_row_commutes_lamps (v w z : ZMod (p ^ 2))
    (hres : Host.residue p v = Host.residue p w) (hne : v ≠ w) (i : Fin L) :
    Commute (baseMap Q p ho hp (PackingBase.row Q (Host.residue p) v w i)) (outputLamp Q p z) := by
  rw [baseMap_row_encoded]
  apply SlotIsolation.row_commutes_all_lamps Q (outputA Q p) (outputT Q p) (outputS Q p)
    (output_a_s Q p) (output_t_s Q p) (output_seed Q p) hp ho (output_period Q p)
    (fun i : Fin L ↦ 2 ^ i.val) (fun i ↦ 2 ^ (i.val + p - 1))
  · intro j
    refine ⟨HostAlgebra.dyadic_pair_distinct hp3 hL ho j, ?_⟩
    simpa only [map_pow, map_ofNat] using
      HostAlgebra.dyadic_pair_same_residue (by omega : 1 ≤ p) ho₁ j.val
  · intro j k hjk
    apply HostAlgebra.dyadic_residue_injective hL ho₁
    simpa only [map_pow, map_ofNat] using hjk
  · intro j
    change Commute (SlotIsolation.storedProduct Q (outputLamp Q p) _ _) (outputLamp Q p j)
    rw [output_storedProduct Q p hp ho]
    exact output_period_commutes_lamps Q p j
  · exact hne
  · exact hres

include hp hp3 hL ho ho₁ in
theorem lower_kernel :
    ⁅PackingBase.kernel Q (Host.residue p), (⊤ : Subgroup (Host.Kernel p))⁆ ≤
      (baseMap Q p ho hp).ker := by
  have hrows (r : Host.Kernel p) (hr : r ∈ PackingBase.rows Q (Host.residue p)) (x : Host.Kernel p) :
      Commute (baseMap Q p ho hp r) (baseMap Q p ho hp x) := by
    apply PackingReduction.commute_all_of_generators (baseMap Q p ho hp)
      (Set.range (Host.lamp p)) (PresentedGroup.closure_range_of _) _ _ x
    rintro _ ⟨z,rfl⟩
    rcases hr with ⟨v,w,hres,hne,i,rfl⟩
    rw [baseMap_lamp]
    exact output_row_commutes_lamps Q p hp hp3 hL ho ho₁ v w z hres hne i
  have hcenter : ∀ r ∈ PackingBase.rows Q (Host.residue p),
      (baseMap Q p ho hp).rangeRestrict r ∈ Subgroup.center (baseMap Q p ho hp).range := by
    intro r hr
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x,hx⟩ := y.property
    apply Subtype.ext
    change y.val * baseMap Q p ho hp r = baseMap Q p ho hp r * y.val
    rw [← hx]
    exact (hrows r hr x).symm
  have h := PackingKernel.commutator_normalClosure_le_kernel
    (baseMap Q p ho hp).rangeRestrict (PackingBase.rows Q (Host.residue p)) hcenter
  simpa only [MonoidHom.ker_rangeRestrict, PackingBase.kernel] using h

include hp hp3 hL ho ho₁ in
/-- The complete absorbed packing embedding, reduced only to the generic signed
code injection into the single factor `B_p`. -/
theorem source_embeds [NeZero p] [Fact (1 < p)]
    (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)
    (hQ : CentrallyClosed Q.Group) (r z : Fin p) (hrz : r ≠ z)
    (hsource : Function.Injective (SignedCoding.sourceHom Q r z hrz)) :
    ∃ f : Q.Group →* (threePresentation Q p).Group, Function.Injective f := by
  let g := PackingBase.quotient Q (Host.residue p)
  have hupper : (baseMap Q p ho hp).ker ≤ g.ker := by
    rw [show g.ker = PackingBase.kernel Q (Host.residue p) from PackingBase.quotient_ker Q _]
    exact upper_kernel Q p u hu hp3 hL ho ho₁ hp
  have hlower : ⁅g.ker, (⊤ : Subgroup (Host.Kernel p))⁆ ≤ (baseMap Q p ho hp).ker := by
    rw [show g.ker = PackingBase.kernel Q (Host.residue p) from PackingBase.quotient_ker Q _]
    exact lower_kernel Q p hp hp3 hL ho ho₁
  exact KernelSandwich.embedding_of_sandwich hQ (baseMap Q p ho hp) g
    (PackingBase.quotient_surjective Q _) hupper hlower
    (PackingBaseProduct.sourceHom Q (Host.residue p) 0 (Host.fiberEquiv p 0) r z hrz)
    (PackingBaseProduct.sourceHom_injective Q (Host.residue p) 0 (Host.fiberEquiv p 0) r z hrz hsource)

end SmallPresentationStatements.AbsorbedPacking
