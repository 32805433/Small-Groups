module

public import SmallPresentation.FourCentralModel
public import SmallPresentation.QuotientKernelTorsion

/-! Transfer the integral central-kernel calculation to the exact four-row group. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral

variable {L : ℕ} (Q : FP 2 L) (p : ℕ) (hp : p.Prime)
    (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

include hp in
theorem basePacked_mem : basePacked Q p ∈ N Q p := by
  apply Subgroup.list_prod_mem
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact Subgroup.subset_normalClosure
    ⟨i.val, ((p + i.val : ℕ) : ZMod (p ^ 2)),
      (FourPacking.slot_pair p hp i).2, (FourPacking.slot_pair p hp i).1, i,rfl⟩

include hp in
theorem packed_mem : packed Q p ∈ RelationExtension.Kernel (N Q p) :=
  (QuotientGroup.eq_one_iff _).mpr (basePacked_mem Q p hp)

theorem action_preserves_kernel (g : HostBS.Group) :
    RelationExtension.Kernel (N Q p) ≤
      (RelationExtension.Kernel (N Q p)).comap (action Q p u hu g).toMonoidHom := by
  intro z hz
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel (N Q p)) z
  have hx : x ∈ N Q p := (QuotientGroup.eq_one_iff _).mp hz
  change RelationExtension.projection (N Q p) (action Q p u hu g (mk Q p x)) = 1
  rw [action_mk]
  exact (QuotientGroup.eq_one_iff _).mpr (kernel_preserved Q p u hu g hx)

noncomputable abbrev packedOrbit := SemidirectOrbit.orbitKernel (action Q p u hu) (packed Q p)

include hp in
theorem packedOrbit_le_kernel : packedOrbit Q p u hu ≤ RelationExtension.Kernel (N Q p) := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g,rfl⟩
  exact action_preserves_kernel Q p u hu g (packed_mem Q p hp)

noncomputable abbrev RemainingKernel :=
  RelationExtension.Kernel (N Q p) ⧸
    (packedOrbit Q p u hu).comap (RelationExtension.Kernel (N Q p)).subtype

include hp in
theorem packedModel_torsionFree (hN : Noncyclic Q.Group) (hT : IsMulTorsionFree Q.Group)
    (hK : IsMulTorsionFree (RemainingKernel Q p u hu)) :
    IsMulTorsionFree (PackedModel Q p u hu) := by
  let : IsMulTorsionFree (C Q p ⧸ packedOrbit Q p u hu) :=
    quotient_torsionFree_of_kernelQuotient (RelationExtension.projection (N Q p))
      (packedOrbit Q p u hu) (packedOrbit_le_kernel Q p hp u hu)
      (FourPacking.base_torsionFree Q p hp hN hT) hK
  let : IsMulTorsionFree HostBS.Group := HostBS.torsionFree
  let : IsMulTorsionFree (SemidirectOrbit.OrbitQuotient (action Q p u hu) (packed Q p)) :=
    Host.semidirect_torsionFree _
  exact (SemidirectOrbit.quotientEquiv (action Q p u hu) (packed Q p)).injective.isMulTorsionFree
    (SemidirectOrbit.quotientEquiv (action Q p u hu) (packed Q p)).toMonoidHom

variable (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1)) (hL : L ≤ p)

include hp ho hL in
theorem output_torsionFree_of_kernel [Fact (1 < p)]
    (hN : Noncyclic Q.Group) (hT : IsMulTorsionFree Q.Group)
    (hK : IsMulTorsionFree (RemainingKernel Q p u hu)) :
    IsMulTorsionFree (fourPresentation Q p).Group :=
  output_torsionFree Q p hp ho hL u hu (packedModel_torsionFree Q p hp u hu hN hT hK)

end SmallPresentationStatements.FourCentral
