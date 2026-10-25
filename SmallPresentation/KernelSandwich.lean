module

public import SmallPresentation.CentralLifting
public import SmallPresentation.Extensions
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# From the two kernel inclusions to the central extension and embedding

The range of the base map is the actual image subgroup of the output group.
The upper inclusion constructs its quotient map; the lower inclusion proves
centrality. Thus the exact-sequence step is a theorem, not an extra assumption.
-/
@[expose] public section

namespace SmallPresentationStatements.KernelSandwich

open scoped commutatorElement

variable {A G B : Type} [Group A] [Group G] [Group B]

noncomputable def rangeProjection (f : A →* G) (g : A →* B) (hker : f.ker ≤ g.ker) :
    f.range →* B :=
  (QuotientGroup.lift f.ker g hker).comp (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom

@[simp] theorem rangeProjection_apply (f : A →* G) (g : A →* B)
    (hker : f.ker ≤ g.ker) (a : A) :
    rangeProjection f g hker (f.rangeRestrict a) = g a := by
  have heq : QuotientGroup.quotientKerEquivRange f (QuotientGroup.mk' f.ker a) =
      f.rangeRestrict a := rfl
  unfold rangeProjection
  rw [MonoidHom.comp_apply, ← heq]
  change QuotientGroup.lift f.ker g hker
    ((QuotientGroup.quotientKerEquivRange f).symm
      ((QuotientGroup.quotientKerEquivRange f) (QuotientGroup.mk' f.ker a))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem rangeProjection_surjective (f : A →* G) (g : A →* B)
    (hker : f.ker ≤ g.ker) (hg : Function.Surjective g) :
    Function.Surjective (rangeProjection f g hker) := by
  intro b
  obtain ⟨a, rfl⟩ := hg b
  exact ⟨f.rangeRestrict a, rangeProjection_apply f g hker a⟩

theorem rangeProjection_kernel (f : A →* G) (g : A →* B) (hker : f.ker ≤ g.ker) :
    (rangeProjection f g hker).ker = g.ker.map f.rangeRestrict := by
  ext y
  obtain ⟨a, ha⟩ := y.property
  have hy : f.rangeRestrict a = y := Subtype.ext ha
  subst y
  constructor
  · intro hy
    have ha : a ∈ g.ker := by
      change g a = 1
      simpa only [MonoidHom.mem_ker, rangeProjection_apply] using hy
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    change rangeProjection f g hker (f.rangeRestrict a) = 1
    rw [← hba, rangeProjection_apply]
    exact hb

theorem rangeProjection_central (f : A →* G) (g : A →* B) (hker : f.ker ≤ g.ker)
    (hcomm : ⁅g.ker, (⊤ : Subgroup A)⁆ ≤ f.ker) :
    ∀ z ∈ (rangeProjection f g hker).ker, ∀ x : f.range, z * x = x * z := by
  intro z hz x
  rw [rangeProjection_kernel] at hz
  obtain ⟨a, ha, rfl⟩ := hz
  obtain ⟨b, hb⟩ := x.property
  have hx : f.rangeRestrict b = x := Subtype.ext hb
  subst x
  apply Subtype.ext
  change f a * f b = f b * f a
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact hcomm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))

/-- The two inclusions alone turn an embedded coded source in `B` into an
embedded source in the actual output `G`. -/
theorem embedding_of_sandwich {Q : Type} [Group Q] (hQ : CentrallyClosed Q)
    (f : A →* G) (g : A →* B) (hg : Function.Surjective g)
    (hupper : f.ker ≤ g.ker) (hlower : ⁅g.ker, (⊤ : Subgroup A)⁆ ≤ f.ker)
    (e : Q →* B) (he : Function.Injective e) :
    ∃ σ : Q →* G, Function.Injective σ := by
  obtain ⟨σ, _, hσ⟩ := hQ.lift_injective (rangeProjection f g hupper)
    (rangeProjection_surjective f g hupper hg) (rangeProjection_central f g hupper hlower) e he
  exact ⟨f.range.subtype.comp σ, Subtype.val_injective.comp hσ⟩

end SmallPresentationStatements.KernelSandwich
