module

public import SmallPresentation.FourCentralWords

/-! The literal four-row group embeds in the centralized packed host.
The inverse map uses the proved lower kernel inclusion on every base generator. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral
open Word

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)
    (hp : p.Prime) (ho : orderOf (2 : ZMod (p ^ 2)) = p * (p - 1))
    (hL : L ≤ p) (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

include hp ho hL in
theorem projection_kernel_killed :
    (projection Q p u hu).ker ≤ (hostModelToOutput Q p hp ho u hu).ker := by
  intro x hx
  have hr : x.right = 1 := congrArg SemidirectProduct.right hx
  have hl : x.left ∈ RelationExtension.commutatorKernel (N Q p) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg SemidirectProduct.left hx
  have hk : FourPacking.baseMap Q p hp ho x.left = 1 := FourPacking.lower_kernel Q p hp ho hL hl
  have heq : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hr
  change hostModelToOutput Q p hp ho u hu x = 1
  rw [heq]
  exact (DFunLike.congr_fun (hostModelToOutput_base Q p hp ho u hu) x.left).trans hk

noncomputable def fromModel : Model Q p u hu →* (fourPresentation Q p).Group :=
  (projection Q p u hu).liftOfSurjective (projection_surjective Q p u hu)
    ⟨hostModelToOutput Q p hp ho u hu, projection_kernel_killed Q p hp ho hL u hu⟩

@[simp] theorem fromModel_projection (x : Host.Model p u hu) :
    fromModel Q p hp ho hL u hu (projection Q p u hu x) = hostModelToOutput Q p hp ho u hu x := by
  simp only [fromModel, MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply]

theorem hostModelToOutput_generators (j : Fin 2) :
    hostModelToOutput Q p hp ho u hu (hostGenerators p u hu j) = PresentedGroup.of j := by
  fin_cases j
  · change hostModelToOutput Q p hp ho u hu (Host.a p u hu * Host.t p u hu) = PresentedGroup.of 0
    rw [map_mul, hostModelToOutput_a, hostModelToOutput_t]
    exact Elimination.recover_b _ _
  · exact hostModelToOutput_s Q p hp ho u hu

theorem fromModel_kills_packed :
    fromModel Q p hp ho hL u hu (SemidirectProduct.inl (packed Q p)) = 1 := by
  change fromModel Q p hp ho hL u hu (SemidirectProduct.inl (mk Q p (basePacked Q p))) = 1
  rw [← projection_inl, fromModel_projection, ← packed_in_host Q p u hu, map_eval]
  simp only [hostModelToOutput_generators]
  exact FourPacking.output_packed Q p

noncomputable def fromPacked : PackedModel Q p u hu →* (fourPresentation Q p).Group :=
  QuotientGroup.lift _ (fromModel Q p hp ho hL u hu) (by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact fromModel_kills_packed Q p hp ho hL u hu)

@[simp] theorem fromPacked_fromHost (x : Host.Model p u hu) :
    fromPacked Q p hp ho hL u hu (fromHost Q p u hu x) = hostModelToOutput Q p hp ho u hu x := by
  change fromModel Q p hp ho hL u hu (projection Q p u hu x) = _
  exact fromModel_projection Q p hp ho hL u hu x

theorem fromPacked_toPacked [Fact (1 < p)] :
    (fromPacked Q p hp ho hL u hu).comp (toPacked Q p u hu) =
      MonoidHom.id (fourPresentation Q p).Group := by
  apply PresentedGroup.ext
  intro j
  simp only [MonoidHom.comp_apply, toPacked_of, generators, fromPacked_fromHost,
    hostModelToOutput_generators, MonoidHom.id_apply]

include hp ho hL in
theorem toPacked_injective [Fact (1 < p)] : Function.Injective (toPacked Q p u hu) := by
  have h : Function.LeftInverse (fromPacked Q p hp ho hL u hu) (toPacked Q p u hu) :=
    DFunLike.congr_fun (fromPacked_toPacked Q p hp ho hL u hu)
  exact h.injective

include hp ho hL in
theorem output_torsionFree [Fact (1 < p)] (h : IsMulTorsionFree (PackedModel Q p u hu)) :
    IsMulTorsionFree (fourPresentation Q p).Group :=
  (toPacked_injective Q p hp ho hL u hu).isMulTorsionFree (toPacked Q p u hu)

end SmallPresentationStatements.FourCentral
