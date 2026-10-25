module

public import Mathlib.GroupTheory.SemidirectProduct

/-! # Quotienting a semidirect product by a relation in its base

The base relations are precisely the normal closure of the acting group's orbit.
This is a general quotient construction, independent of the packed presentations.
-/
@[expose] public section

namespace SmallPresentationStatements.SemidirectOrbit

variable {C G : Type*} [Group C] [Group G] (α : G →* MulAut C)
variable (M : Subgroup C) [M.Normal]
variable (hM : ∀ g, M ≤ M.comap (α g).toMonoidHom)

def quotientMap (g : G) : C ⧸ M →* C ⧸ M :=
  QuotientGroup.map M M (α g).toMonoidHom (hM g)

@[simp] theorem quotientMap_mk (g : G) (x : C) :
    quotientMap α M hM g (QuotientGroup.mk' M x) = QuotientGroup.mk' M (α g x) := rfl

def quotientAut (g : G) : MulAut (C ⧸ M) where
  toFun := quotientMap α M hM g
  invFun := quotientMap α M hM g⁻¹
  left_inv := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective M q
    change QuotientGroup.mk' M (α g⁻¹ (α g x)) = QuotientGroup.mk' M x
    simp [map_inv]
  right_inv := by
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective M q
    change QuotientGroup.mk' M (α g (α g⁻¹ x)) = QuotientGroup.mk' M x
    simp [map_inv]
  map_mul' := map_mul _

def quotientAction : G →* MulAut (C ⧸ M) where
  toFun := quotientAut α M hM
  map_one' := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective M q
    change QuotientGroup.mk' M (α 1 x) = QuotientGroup.mk' M x
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective M q
    change QuotientGroup.mk' M (α (g*h) x) = QuotientGroup.mk' M (α g (α h x))
    rw [map_mul]
    rfl

@[simp] theorem quotientAction_mk (g : G) (x : C) :
    quotientAction α M hM g (QuotientGroup.mk' M x) = QuotientGroup.mk' M (α g x) := rfl

def projection : C ⋊[α] G →* (C ⧸ M) ⋊[quotientAction α M hM] G :=
  SemidirectProduct.map (QuotientGroup.mk' M) (MonoidHom.id G) (fun _ ↦ rfl)

theorem projection_surjective : Function.Surjective (projection α M hM) := by
  intro q
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective M q.left
  refine ⟨⟨x,q.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact hx
  · rfl

variable (w : C)

abbrev orbitKernel : Subgroup C := Subgroup.normalClosure (Set.range fun g ↦ α g w)

theorem orbitKernel_invariant (g : G) :
    orbitKernel α w ≤ (orbitKernel α w).comap (α g).toMonoidHom := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨h,rfl⟩
  change α g (α h w) ∈ orbitKernel α w
  have hm : α g (α h w) = α (g*h) w := by rw [map_mul]; rfl
  rw [hm]
  exact Subgroup.subset_normalClosure ⟨g*h,rfl⟩

abbrev totalKernel : Subgroup (C ⋊[α] G) :=
  Subgroup.normalClosure {SemidirectProduct.inl w}

noncomputable abbrev OrbitQuotient :=
  (C ⧸ orbitKernel α w) ⋊[quotientAction α (orbitKernel α w) (orbitKernel_invariant α w)] G

def orbitProjection : C ⋊[α] G →* OrbitQuotient α w :=
  projection α (orbitKernel α w) (orbitKernel_invariant α w)

theorem orbitProjection_ker : (orbitProjection α w).ker = totalKernel α w := by
  apply le_antisymm
  · intro x hx
    have hr : x.right = 1 := congrArg SemidirectProduct.right hx
    have hl : x.left ∈ orbitKernel α w := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg SemidirectProduct.left hx
    have hm : orbitKernel α w ≤ (totalKernel α w).comap SemidirectProduct.inl := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨g,rfl⟩
      change SemidirectProduct.inl (α g w) ∈ totalKernel α w
      rw [SemidirectProduct.inl_aut]
      simpa only [map_inv] using
        Subgroup.Normal.conj_mem (inferInstance : (totalKernel α w).Normal) _
          (Subgroup.subset_normalClosure (Set.mem_singleton _)) (SemidirectProduct.inr g)
    have heq : x = SemidirectProduct.inl x.left := by
      apply SemidirectProduct.ext
      · rfl
      · exact hr
    rw [heq]
    exact hm hl
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    apply SemidirectProduct.ext
    · change QuotientGroup.mk' (orbitKernel α w) w = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      apply Subgroup.subset_normalClosure
      exact ⟨1, by simp⟩
    · rfl

/-- The full quotient is exactly the semidirect product of the base orbit quotient. -/
noncomputable def quotientEquiv :
    (C ⋊[α] G) ⧸ totalKernel α w ≃* OrbitQuotient α w :=
  (QuotientGroup.quotientMulEquivOfEq (orbitProjection_ker α w).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (orbitProjection α w)
      (projection_surjective α (orbitKernel α w) (orbitKernel_invariant α w)))

@[simp] theorem quotientEquiv_mk (x : C ⋊[α] G) :
    quotientEquiv α w (QuotientGroup.mk' (totalKernel α w) x) = orbitProjection α w x := rfl

end SmallPresentationStatements.SemidirectOrbit
