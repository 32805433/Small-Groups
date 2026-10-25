module

public import SmallPresentation.PackingBase
public import SmallPresentation.CentralProduct
public import SmallPresentation.SemidirectOrbit

/-! The actual Baumslag–Solitar action on the central relation quotient. -/
@[expose] public section

namespace SmallPresentationStatements.FourCentral

variable {L : ℕ} (Q : FP 2 L) (p : ℕ)

abbrev N := PackingBase.kernel Q (Host.residue p)
abbrev C := RelationExtension.Total (N Q p)

def mk : Host.Kernel p →* C Q p := QuotientGroup.mk' _
def lamp (v : ZMod (p ^ 2)) : C Q p := mk Q p (Host.lamp p v)

private def preservingSubgroup {D G : Type} [Group D] [Group G]
    (α : G →* MulAut D) (R : Subgroup D) : Subgroup G where
  carrier := {g | ∀ x, α g x ∈ R ↔ x ∈ R}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [map_mul]
    change α g (α h x) ∈ R ↔ x ∈ R
    exact (hg _).trans (hh _)
  inv_mem' := by
    intro g hg x
    have h := hg ((α g)⁻¹ x)
    simpa only [map_inv, MulAut.apply_inv_self] using h.symm

private theorem perm_preserves (e : Equiv.Perm (ZMod (p ^ 2)))
    (he : ∀ v w, Host.residue p (e v) = Host.residue p (e w) ↔
      Host.residue p v = Host.residue p w) (x : Host.Kernel p) :
    HostPartition.permAut (Host.residue p) e he x ∈ N Q p ↔ x ∈ N Q p := by
  constructor
  · intro hx
    have h := PackingBase.kernel_preserved Q (Host.residue p) e.symm
      (HostPartition.partition_symm (Host.residue p) e he) hx
    change (HostPartition.permAut (Host.residue p) e he)⁻¹
      (HostPartition.permAut (Host.residue p) e he x) ∈ N Q p at h
    simpa only [MulAut.inv_apply_self] using h
  · intro hx
    exact PackingBase.kernel_preserved Q (Host.residue p) e he hx

variable (u : (ZMod (p ^ 2))ˣ) (hu : (u : ZMod (p ^ 2)) = 2)

theorem action_mem_iff (g : HostBS.Group) (x : Host.Kernel p) :
    Host.action p u hu g x ∈ N Q p ↔ x ∈ N Q p := by
  have h : g ∈ preservingSubgroup (Host.action p u hu) (N Q p) := by
    apply HostBS.generated_by
    · intro x
      rw [Host.action_t]
      have h := perm_preserves Q p (Host.shiftPerm p) (Host.shift_partition p)
        ((Host.shift p)⁻¹ x)
      change Host.shift p ((Host.shift p)⁻¹ x) ∈ N Q p ↔ _ at h
      simpa only [MulAut.apply_inv_self] using h.symm
    · intro x
      rw [Host.action_s]
      have h := perm_preserves Q p (Host.doublePerm p u) (Host.double_partition p u)
        ((Host.doubling p u)⁻¹ x)
      change Host.doubling p u ((Host.doubling p u)⁻¹ x) ∈ N Q p ↔ _ at h
      simpa only [MulAut.apply_inv_self] using h.symm
  exact h x

theorem kernel_preserved (g : HostBS.Group) :
    N Q p ≤ (N Q p).comap (Host.action p u hu g).toMonoidHom :=
  fun x hx ↦ (action_mem_iff Q p u hu g x).mpr hx

theorem action_kernel_map (g : HostBS.Group) :
    (N Q p).map (Host.action p u hu g).toMonoidHom = N Q p := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact kernel_preserved Q p u hu g hx
  · intro x hx
    refine ⟨(Host.action p u hu g)⁻¹ x, ?_, by simp⟩
    apply (action_mem_iff Q p u hu g _).mp
    simpa only [MulAut.apply_inv_self] using hx

theorem commutator_preserved (g : HostBS.Group) :
    RelationExtension.commutatorKernel (N Q p) ≤
      (RelationExtension.commutatorKernel (N Q p)).comap (Host.action p u hu g).toMonoidHom := by
  apply Subgroup.map_le_iff_le_comap.mp
  rw [CentralRelationMap.map_commutatorKernel (N Q p) (N Q p)
    (Host.action p u hu g) (action_kernel_map Q p u hu g)]

noncomputable def action : HostBS.Group →* MulAut (C Q p) :=
  SemidirectOrbit.quotientAction (Host.action p u hu)
    (RelationExtension.commutatorKernel (N Q p)) (commutator_preserved Q p u hu)

@[simp] theorem action_mk (g : HostBS.Group) (x : Host.Kernel p) :
    action Q p u hu g (mk Q p x) = mk Q p (Host.action p u hu g x) := rfl

@[simp] theorem action_t_lamp (v : ZMod (p ^ 2)) :
    action Q p u hu HostBS.t (lamp Q p v) = lamp Q p (v - 1) := by
  simp only [lamp, action_mk, Host.action_t, Host.shift_inv_lamp]

@[simp] theorem action_s_lamp (v : ZMod (p ^ 2)) :
    action Q p u hu HostBS.s (lamp Q p v) = lamp Q p (u⁻¹ * v) := by
  simp only [lamp, action_mk, Host.action_s, Host.doubling_inv_lamp]

@[simp] theorem action_t_inv_lamp (v : ZMod (p ^ 2)) :
    action Q p u hu HostBS.t⁻¹ (lamp Q p v) = lamp Q p (v + 1) := by
  unfold lamp
  rw [action_mk]
  simp only [map_inv, Host.action_t, inv_inv, Host.shift_lamp]

@[simp] theorem action_s_inv_lamp (v : ZMod (p ^ 2)) :
    action Q p u hu HostBS.s⁻¹ (lamp Q p v) = lamp Q p (u * v) := by
  unfold lamp
  rw [action_mk]
  simp only [map_inv, Host.action_s, inv_inv, Host.doubling_lamp]

noncomputable abbrev Model := C Q p ⋊[action Q p u hu] HostBS.Group

noncomputable def projection : Host.Model p u hu →* Model Q p u hu :=
  SemidirectOrbit.projection (Host.action p u hu)
    (RelationExtension.commutatorKernel (N Q p)) (commutator_preserved Q p u hu)

theorem projection_surjective : Function.Surjective (projection Q p u hu) :=
  SemidirectOrbit.projection_surjective _ _ _

@[simp] theorem projection_inl (x : Host.Kernel p) :
    projection Q p u hu (SemidirectProduct.inl x) = SemidirectProduct.inl (mk Q p x) := rfl

@[simp] theorem projection_inr (g : HostBS.Group) :
    projection Q p u hu (SemidirectProduct.inr g) = SemidirectProduct.inr g := by
  exact SemidirectProduct.map_inr (mk Q p) (MonoidHom.id HostBS.Group) (fun _ ↦ rfl) g

end SmallPresentationStatements.FourCentral
