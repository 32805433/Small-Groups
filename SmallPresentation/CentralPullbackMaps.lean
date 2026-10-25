module

public import SmallPresentation.CentralLifting

/-! Canonical kernel inclusions and equivalences over the base for group pullbacks. -/
@[expose] public section

namespace SmallPresentationStatements.CentralPullback

variable {E G A : Type} [Group E] [Group G] [Group A]
variable (π : E →* G) (l r : A →* G)

def kernelInclusion : π.ker →* group π l where
  toFun z := ⟨(z,1), by change π z = l 1; rw [map_one]; exact z.property⟩
  map_one' := rfl
  map_mul' _ _ := by apply Subtype.ext; exact Prod.ext rfl (one_mul _).symm

@[simp] theorem first_kernelInclusion (z : π.ker) : first π l (kernelInclusion π l z) = z := rfl

@[simp] theorem second_kernelInclusion (z : π.ker) : second π l (kernelInclusion π l z) = 1 := rfl

theorem first_injective (hl : Function.Injective l) : Function.Injective (first π l) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · apply hl
    exact x.property.symm.trans ((congrArg π h).trans y.property)

/-- An equivalence of pullback extensions over the edge group and its central kernel. -/
structure OverEquiv where
  equiv : group π l ≃* group π r
  over : (second π r).comp equiv.toMonoidHom = second π l
  kernel : ∀ z : π.ker, equiv (kernelInclusion π l z) = kernelInclusion π r z

namespace OverEquiv

variable {π l r} (e : OverEquiv π l r)

@[simp] theorem second_equiv (x : group π l) : second π r (e.equiv x) = second π l x :=
  DFunLike.congr_fun e.over x

noncomputable def symm : OverEquiv π r l where
  equiv := e.equiv.symm
  over := by
    apply MonoidHom.ext
    intro x
    have h := e.second_equiv (e.equiv.symm x)
    simpa using h.symm
  kernel z := by
    apply e.equiv.injective
    rw [e.equiv.apply_symm_apply, e.kernel]

end OverEquiv
end SmallPresentationStatements.CentralPullback
