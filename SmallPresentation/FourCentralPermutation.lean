module

public import SmallPresentation.FourCentralAction

/-! Every acting Baumslag–Solitar element permutes the lamps and their partition. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)
variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

private def permutationSubgroup : Subgroup HostBS.Group where
  carrier := {g | ∃ σ : Equiv.Perm (ZMod (p ^ 2)),
    (∀ v w, Host.residue p (σ v) = Host.residue p (σ w) ↔
      Host.residue p v = Host.residue p w) ∧
    ∀ v, action Q p u hu g (lamp Q p v) = lamp Q p (σ v)}
  one_mem' := by
    refine ⟨Equiv.refl _, ?_, ?_⟩
    · intro v w; rfl
    · intro v; simp
  mul_mem' := by
    rintro g h ⟨σ,hσ,hg⟩ ⟨τ,hτ,hh⟩
    refine ⟨τ.trans σ, ?_, ?_⟩
    · intro v w
      exact (hσ (τ v) (τ w)).trans (hτ v w)
    · intro v
      rw [map_mul]
      change action Q p u hu g (action Q p u hu h (lamp Q p v)) = _
      rw [hh, hg]
      rfl
  inv_mem' := by
    rintro g ⟨σ,hσ,hg⟩
    refine ⟨σ.symm, HostPartition.partition_symm (Host.residue p) σ hσ, ?_⟩
    intro v
    apply (action Q p u hu g).injective
    rw [map_inv]
    change action Q p u hu g ((action Q p u hu g)⁻¹ (lamp Q p v)) = _
    rw [MulAut.apply_inv_self, hg, σ.apply_symm_apply]

/-- Every group element acts by a permutation preserving the residue partition. -/
theorem action_permutation (g : HostBS.Group) :
    ∃ σ : Equiv.Perm (ZMod (p ^ 2)),
      (∀ v w, Host.residue p (σ v) = Host.residue p (σ w) ↔
        Host.residue p v = Host.residue p w) ∧
      ∀ v, action Q p u hu g (lamp Q p v) = lamp Q p (σ v) := by
  have hg : g ∈ permutationSubgroup Q p u hu := by
    apply HostBS.generated_by
    · refine ⟨(Host.shiftPerm p).symm,
        HostPartition.partition_symm (Host.residue p) (Host.shiftPerm p) (Host.shift_partition p), ?_⟩
      intro v
      exact action_t_lamp Q p u hu v
    · refine ⟨(Host.doublePerm p u).symm,
        HostPartition.partition_symm (Host.residue p) (Host.doublePerm p u) (Host.double_partition p u), ?_⟩
      intro v
      exact action_s_lamp Q p u hu v
  exact hg

end SmallPresentationStatements.FourCentral
