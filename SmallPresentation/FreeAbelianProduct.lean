module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.BigOperators.Pi

/-! A finite product of free abelian groups has the disjoint union of their bases. -/
@[expose] public section

namespace SmallPresentationStatements.FreeAbelianProduct

open scoped BigOperators

variable {C : Type*} [Fintype C] [DecidableEq C] (I : C → Type*)

noncomputable def toProduct : FreeAbelianGroup (Σ c, I c) →+ (∀ c, FreeAbelianGroup (I c)) :=
  FreeAbelianGroup.lift fun p ↦ Pi.single p.1 (FreeAbelianGroup.of p.2)

noncomputable def fromProduct : (∀ c, FreeAbelianGroup (I c)) →+ FreeAbelianGroup (Σ c, I c) where
  toFun x := ∑ c, FreeAbelianGroup.map (Sigma.mk c) (x c)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

omit [Fintype C] in
@[simp] theorem toProduct_of (p : Σ c, I c) :
    toProduct I (FreeAbelianGroup.of p) = Pi.single p.1 (FreeAbelianGroup.of p.2) :=
  FreeAbelianGroup.lift_apply_of _ _

@[simp] theorem fromProduct_single (c : C) (x : FreeAbelianGroup (I c)) :
    fromProduct I (Pi.single c x) = FreeAbelianGroup.map (Sigma.mk c) x := by
  change (∑ j, FreeAbelianGroup.map (Sigma.mk j) ((Pi.single c x : ∀ c, FreeAbelianGroup (I c)) j)) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro b hb hbc
    simp [Pi.single_eq_of_ne hbc]
  · simp

omit [Fintype C] in
@[simp] theorem toProduct_map (c : C) (x : FreeAbelianGroup (I c)) :
    toProduct I (FreeAbelianGroup.map (Sigma.mk c) x) = Pi.single c x := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of i => simp [FreeAbelianGroup.map, toProduct_of]
  | neg x hx => simpa only [map_neg, Pi.single_neg] using congrArg Neg.neg hx
  | add x y hx hy => simp [hx, hy, Pi.single_add]

noncomputable def sigmaEquiv : FreeAbelianGroup (Σ c, I c) ≃+ (∀ c, FreeAbelianGroup (I c)) where
  toFun := toProduct I
  invFun := fromProduct I
  left_inv x := by
    have h : (fromProduct I).comp (toProduct I) = AddMonoidHom.id _ := by
      apply FreeAbelianGroup.lift_ext
      intro p
      simp [FreeAbelianGroup.map, AddMonoidHom.comp_apply]
    exact DFunLike.congr_fun h x
  right_inv x := by
    change toProduct I (∑ c, FreeAbelianGroup.map (Sigma.mk c) (x c)) = x
    rw [map_sum]
    simp only [toProduct_map]
    ext c
    simp
  map_add' := map_add _

@[simp] theorem sigmaEquiv_of (p : Σ c, I c) :
    sigmaEquiv I (FreeAbelianGroup.of p) = Pi.single p.1 (FreeAbelianGroup.of p.2) :=
  toProduct_of I p

end SmallPresentationStatements.FreeAbelianProduct
