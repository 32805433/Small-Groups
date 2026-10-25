module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import Mathlib.Algebra.Group.Pi.Torsion

/-! The group with one free generator per vertex and commutations exactly
between distinct blocks is the direct product of the free groups on the blocks. -/
@[expose] public section

namespace SmallPresentationStatements.HostPartition

open scoped commutatorElement

variable {V C : Type*} (π : V → C)

def relations : Set (FreeGroup V) :=
  {w | ∃ v u, π v ≠ π u ∧ w = ⁅FreeGroup.of v, FreeGroup.of u⁆}

abbrev Group := PresentedGroup (relations π)
abbrev Product := ∀ c : C, FreeGroup {v : V // π v = c}

def generator (v : V) : Group π := PresentedGroup.of v

theorem generators_commute (v u : V) (h : π v ≠ π u) :
    Commute (generator π v) (generator π u) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have hr := PresentedGroup.one_of_mem (rels := relations π) ⟨v, u, h, rfl⟩
  simpa only [commutatorElement_def, map_mul, map_inv, generator, PresentedGroup.of] using hr

theorem free_lifts_commute {A B H : Type*} [_root_.Group H] (f : FreeGroup A →* H)
    (g : FreeGroup B →* H) (h : ∀ a b, Commute (f (FreeGroup.of a)) (g (FreeGroup.of b)))
    (a : FreeGroup A) (b : FreeGroup B) : Commute (f a) (g b) := by
  induction a using FreeGroup.induction_on with
  | one => simp
  | of a =>
    induction b using FreeGroup.induction_on with
    | one => simp
    | of b => exact h a b
    | inv_of b hb => simpa only [map_inv] using hb.inv_right
    | mul b c hb hc => simpa only [map_mul] using hb.mul_right hc
  | inv_of a ha => simpa only [map_inv] using ha.inv_left
  | mul a b ha hb => simpa only [map_mul] using ha.mul_left hb

def factor (c : C) : FreeGroup {v : V // π v = c} →* Group π :=
  FreeGroup.lift (fun v ↦ generator π v.1)

theorem factors_commute : Pairwise fun c d ↦ ∀ a b, Commute (factor π c a) (factor π d b) := by
  intro c d h a b
  apply free_lifts_commute
  intro v u
  apply generators_commute
  simpa only [v.property, u.property] using h

section Finite
variable [Fintype C] [DecidableEq C]

def fromProduct : Product π →* Group π := MonoidHom.noncommPiCoprod (factor π) (factors_commute π)

def productGenerator (v : V) : Product π :=
  Pi.mulSingle (π v) (FreeGroup.of ⟨v, rfl⟩)

omit [Fintype C] in
theorem productGenerators_commute (v u : V) (h : π v ≠ π u) :
    Commute (productGenerator π v) (productGenerator π u) := Pi.mulSingle_commute h _ _

def toProduct : Group π →* Product π :=
  PresentedGroup.toGroup (f := productGenerator π) (by
    rintro _ ⟨v, u, h, rfl⟩
    simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact (commutatorElement_eq_one_iff_commute.mpr (productGenerators_commute π v u h)))

omit [Fintype C] in
@[simp] theorem toProduct_generator (v : V) :
    toProduct π (generator π v) = productGenerator π v := PresentedGroup.toGroup.of _

@[simp] theorem fromProduct_generator (v : V) :
    fromProduct π (productGenerator π v) = generator π v := by
  simp [fromProduct, productGenerator, factor]

theorem from_to : (fromProduct π).comp (toProduct π) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro v
  change fromProduct π (toProduct π (generator π v)) = generator π v
  simp

theorem to_from : (toProduct π).comp (fromProduct π) = MonoidHom.id _ := by
  apply MonoidHom.pi_ext
  intro c
  have h : ((toProduct π).comp (factor π c)) =
      MonoidHom.mulSingle (fun c ↦ FreeGroup {v : V // π v = c}) c := by
    apply FreeGroup.ext_hom
    intro v
    simp only [MonoidHom.comp_apply, factor, FreeGroup.lift_apply_of, toProduct_generator,
      MonoidHom.mulSingle_apply]
    rcases v with ⟨v, hv⟩
    subst c
    rfl
  intro a
  simpa only [MonoidHom.comp_apply, fromProduct, MonoidHom.noncommPiCoprod_mulSingle,
    MonoidHom.id_apply, MonoidHom.mulSingle_apply] using DFunLike.congr_fun h a

def productEquiv : Group π ≃* Product π where
  toFun := toProduct π
  invFun := fromProduct π
  left_inv a := DFunLike.congr_fun (from_to π) a
  right_inv a := DFunLike.congr_fun (to_from π) a
  map_mul' := (toProduct π).map_mul

theorem torsionFree : IsMulTorsionFree (Group π) :=
  (productEquiv π).injective.isMulTorsionFree (productEquiv π).toMonoidHom

end Finite

/-- A vertex permutation preserving the partition induces a group automorphism. -/
def permMap (e : Equiv.Perm V) (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) :
    Group π →* Group π :=
  PresentedGroup.toGroup (f := fun v ↦ generator π (e v)) (by
    rintro _ ⟨v, u, h, rfl⟩
    simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
    exact commutatorElement_eq_one_iff_commute.mpr
      (generators_commute π _ _ (fun hh ↦ h ((he v u).mp hh))))

@[simp] theorem permMap_generator (e : Equiv.Perm V)
    (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) (v : V) :
    permMap π e he (generator π v) = generator π (e v) := PresentedGroup.toGroup.of _

theorem partition_symm (e : Equiv.Perm V) (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) :
    ∀ v u, π (e.symm v) = π (e.symm u) ↔ π v = π u := by
  intro v u
  simpa using (he (e.symm v) (e.symm u)).symm

def permAut (e : Equiv.Perm V) (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) :
    MulAut (Group π) where
  toFun := permMap π e he
  invFun := permMap π e.symm (partition_symm π e he)
  left_inv a := by
    have h : (permMap π e.symm (partition_symm π e he)).comp (permMap π e he) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      intro v
      change permMap π e.symm (partition_symm π e he)
        (permMap π e he (generator π v)) = generator π v
      simp
    exact DFunLike.congr_fun h a
  right_inv a := by
    have h : (permMap π e he).comp (permMap π e.symm (partition_symm π e he)) = MonoidHom.id _ := by
      apply PresentedGroup.ext
      intro v
      change permMap π e he (permMap π e.symm (partition_symm π e he) (generator π v)) =
        generator π v
      simp
    exact DFunLike.congr_fun h a
  map_mul' := (permMap π e he).map_mul

@[simp] theorem permAut_generator (e : Equiv.Perm V)
    (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) (v : V) :
    permAut π e he (generator π v) = generator π (e v) := permMap_generator π e he v

@[simp] theorem permAut_inv_generator (e : Equiv.Perm V)
    (he : ∀ v u, π (e v) = π (e u) ↔ π v = π u) (v : V) :
    (permAut π e he)⁻¹ (generator π v) = generator π (e.symm v) :=
  permMap_generator π e.symm (partition_symm π e he) v

end SmallPresentationStatements.HostPartition
