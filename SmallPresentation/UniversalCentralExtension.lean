module

public import SmallPresentation.RelationExtension
public import Mathlib.Tactic.Group

/-!
# Universal central extensions of perfect quotients of free groups

This module proves the elementary central-extension algebra and the universal lifting
property of the derived subgroup of the central relation extension.
-/
@[expose] public section

namespace SmallPresentationStatements.UniversalCentralExtension

open scoped commutatorElement

variable {E Q U : Type} [Group E] [Group Q] [Group U]

/-- The subgroup formulation of a central kernel. -/
def Central (π : E →* Q) : Prop := π.ker ≤ Subgroup.center E

theorem central_iff (π : E →* Q) : Central π ↔
    ∀ z ∈ π.ker, ∀ x : E, z * x = x * z := by
  constructor
  · intro h z hz x
    exact (Subgroup.mem_center_iff.mp (h hz) x).symm
  · intro h z hz
    exact Subgroup.mem_center_iff.mpr fun x ↦ (h z hz x).symm

theorem derived_sup_kernel (π : E →* Q) (hπ : Function.Surjective π)
    (hQ : commutator Q = ⊤) : commutator E ⊔ π.ker = ⊤ := by
  rw [← Subgroup.comap_map_eq, map_commutator_of_surjective hπ, hQ, Subgroup.comap_top]

theorem commutator_kernel (π : E →* Q) (hc : Central π) (S : Subgroup E) :
    ⁅π.ker, S⁆ = ⊥ := by
  apply le_antisymm _ bot_le
  exact (Subgroup.commutator_mono hc le_rfl).trans_eq (Subgroup.commutator_center_left S)

/-- The derived group of a central extension of a perfect group is itself perfect. -/
theorem derived_perfect (π : E →* Q) (hπ : Function.Surjective π)
    (hc : Central π) (hQ : commutator Q = ⊤) :
    commutator (commutator E) = ⊤ := by
  have hs := derived_sup_kernel π hπ hQ
  let : (commutator E ⊔ π.ker).Normal := Subgroup.Normal.of_commutator_le E le_sup_left
  have heq : ⁅commutator E ⊔ π.ker, commutator E ⊔ π.ker⁆ =
      ⁅commutator E, commutator E⁆ := by
    rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
      commutator_kernel π hc, Subgroup.commutator_comm (commutator E) π.ker,
      commutator_kernel π hc]
    simp
  rw [hs] at heq
  apply Subgroup.map_injective (commutator E).subtype_injective
  rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact heq.symm

/-- In a central extension of a perfect group, preimages of central elements are central. -/
theorem preimage_center (π : E →* Q) (hπ : Function.Surjective π)
    (hc : Central π) (hQ : commutator Q = ⊤) :
    (Subgroup.center Q).comap π ≤ Subgroup.center E := by
  let Z := (Subgroup.center Q).comap π
  have hz : ⁅Z, (⊤ : Subgroup E)⁆ ≤ π.ker := by
    apply Subgroup.commutator_le.mpr
    intro z hz x _
    change π ⁅z, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp hz (π x)).symm
  have hzt : ⁅⁅Z, (⊤ : Subgroup E)⁆, (⊤ : Subgroup E)⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    exact (Subgroup.commutator_mono hz le_rfl).trans_eq (commutator_kernel π hc ⊤)
  have hdz : ⁅commutator E, Z⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (by simpa only [Subgroup.commutator_comm (⊤ : Subgroup E) Z] using hzt) hzt
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  rw [← derived_sup_kernel π hπ hQ, Subgroup.commutator_sup_left,
    Subgroup.commutator_comm Z (commutator E), hdz,
    Subgroup.commutator_comm Z π.ker, commutator_kernel π hc]
  simp

/-- Composition stays central when the middle group is perfect. -/
theorem central_comp (π : E →* U) (p : U →* Q) (hπ : Function.Surjective π)
    (hπc : Central π) (hpc : Central p) (hU : commutator U = ⊤) :
    Central (p.comp π) := by
  intro z hz
  apply preimage_center π hπ hπc hU
  exact hpc hz

def differenceHom (π : E →* Q) (hc : Central π) (f g : U →* E)
    (heq : π.comp f = π.comp g) : U →* E where
  toFun x := f x * (g x)⁻¹
  map_one' := by simp
  map_mul' x y := by
    have hy : f y * (g y)⁻¹ ∈ π.ker := by
      change π (f y * (g y)⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [show π (f y) = π (g y) from DFunLike.congr_fun heq y]
      exact mul_inv_cancel _
    have hcomm := (central_iff π).mp hc (f y * (g y)⁻¹) hy ((g x)⁻¹)
    simp only [map_mul, mul_inv_rev]
    calc
      f x * f y * ((g y)⁻¹ * (g x)⁻¹) = f x * ((f y * (g y)⁻¹) * (g x)⁻¹) := by group
      _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := by rw [hcomm]
      _ = _ := by group

/-- Two lifts from a perfect group into a central extension are equal. -/
theorem lift_unique (π : E →* Q) (hc : Central π) (hU : commutator U = ⊤)
    (f g : U →* E) (heq : π.comp f = π.comp g) : f = g := by
  let δ := differenceHom π hc f g heq
  have hδ (x : U) : δ x ∈ π.ker := by
    change π (f x * (g x)⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [show π (f x) = π (g x) from DFunLike.congr_fun heq x]
    exact mul_inv_cancel _
  have hkill : commutator U ≤ δ.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change δ ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (central_iff π).mp hc _ (hδ x) _
  ext x
  have hx : δ x = 1 := hkill (hU ▸ Subgroup.mem_top x)
  exact mul_inv_eq_one.mp hx

/-- Universal lifting into central extensions, together with a perfect domain,
forces every central extension of the domain to split. -/
theorem centrallyClosed_of_universal (p : U →* Q) (hp : Function.Surjective p)
    (hpc : Central p) (hU : commutator U = ⊤)
    (hlift : ∀ (D : Type) [Group D] (q : D →* Q),
      Function.Surjective q → Central q → ∃ f : U →* D, q.comp f = p) :
    CentrallyClosed U := by
  intro E _ π hπ hc
  have hπc : Central π := (central_iff π).mpr hc
  obtain ⟨σ, hσ⟩ := hlift E (p.comp π) (hp.comp hπ) (central_comp π p hπ hπc hpc hU)
  refine ⟨σ, lift_unique p hpc hU (π.comp σ) (MonoidHom.id U) ?_⟩
  simpa only [MonoidHom.comp_assoc, MonoidHom.comp_id] using hσ

section FreePresentation

variable {X : Type} (N : Subgroup (FreeGroup X)) [N.Normal]

abbrev Derived := commutator (RelationExtension.Total N)

def derivedProjection : Derived N →* FreeGroup X ⧸ N :=
  (RelationExtension.projection N).comp (Derived N).subtype

theorem derivedProjection_surjective
    (hQ : commutator (FreeGroup X ⧸ N) = ⊤) :
    Function.Surjective (derivedProjection N) := by
  intro q
  have hmem : q ∈ (Derived N).map (RelationExtension.projection N) := by
    rw [map_commutator_of_surjective (RelationExtension.projection_surjective N), hQ]
    trivial
  obtain ⟨z, hz, heq⟩ := hmem
  exact ⟨⟨z, hz⟩, heq⟩

theorem derivedProjection_central : Central (derivedProjection N) := by
  apply (central_iff _).mpr
  intro z hz x
  apply Subtype.ext
  exact RelationExtension.kernel_central N z.val hz x.val

theorem relationDerived_perfect (hQ : commutator (FreeGroup X ⧸ N) = ⊤) :
    commutator (Derived N) = ⊤ :=
  derived_perfect (RelationExtension.projection N) (RelationExtension.projection_surjective N)
    ((central_iff _).mpr (RelationExtension.kernel_central N)) hQ

/-- Freeness lifts the generators; centrality kills `[N,F]`, so the lift descends
through the relation extension and restricts to its derived subgroup. -/
theorem relationDerived_lift (D : Type) [Group D] (π : D →* FreeGroup X ⧸ N)
    (hπ : Function.Surjective π) (hc : Central π) :
    ∃ f : Derived N →* D, π.comp f = derivedProjection N := by
  classical
  let liftGenerator : X → D := fun x ↦
    Classical.choose (hπ (QuotientGroup.mk' N (FreeGroup.of x)))
  have hlift (x : X) : π (liftGenerator x) = QuotientGroup.mk' N (FreeGroup.of x) :=
    Classical.choose_spec (hπ (QuotientGroup.mk' N (FreeGroup.of x)))
  let f : FreeGroup X →* D := FreeGroup.lift liftGenerator
  have hf : π.comp f = QuotientGroup.mk' N := by
    apply FreeGroup.ext_hom
    intro x
    simpa only [MonoidHom.comp_apply, f, FreeGroup.lift_apply_of] using hlift x
  have hN (x : FreeGroup X) (hx : x ∈ N) : f x ∈ π.ker := by
    change π (f x) = 1
    rw [show π (f x) = QuotientGroup.mk' N x from DFunLike.congr_fun hf x]
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hkill : RelationExtension.commutatorKernel N ≤ f.ker := by
    apply Subgroup.commutator_le.mpr
    intro n hn x _
    change f ⁅n, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (central_iff π).mp hc (f n) (hN n hn) (f x)
  let k : RelationExtension.Total N →* D :=
    QuotientGroup.lift (RelationExtension.commutatorKernel N) f hkill
  have hk : π.comp k = RelationExtension.projection N := by
    apply MonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel N) z
    exact DFunLike.congr_fun hf x
  refine ⟨k.comp (Derived N).subtype, ?_⟩
  ext z
  exact DFunLike.congr_fun hk z.val

/-- The derived central relation extension of a perfect quotient of a free group
is centrally closed. This is the universal-central-extension theorem, proved
here from free lifting, commutator identities, and uniqueness over a perfect group. -/
theorem relationDerived_centrallyClosed (hQ : commutator (FreeGroup X ⧸ N) = ⊤) :
    CentrallyClosed (commutator (RelationExtension.Total N)) := by
  apply centrallyClosed_of_universal (derivedProjection N)
    (derivedProjection_surjective N hQ) (derivedProjection_central N)
    (relationDerived_perfect N hQ)
  exact relationDerived_lift N

end FreePresentation

end SmallPresentationStatements.UniversalCentralExtension
