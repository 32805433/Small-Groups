module

public import SmallPresentation.Homology
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! Commutators of lifts of commuting group homomorphisms into a central
extension give a canonical pairing on the two abelianizations. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable {E Q G H : Type} [Group E] [Group Q] [Group G] [Group H]
variable (π : E →* Q) (hc : UniversalCentralExtension.Central π)

include hc

theorem commutator_eq_of_projection_eq_left {a a' b : E} (h : π a = π a') :
    ⁅a,b⁆ = ⁅a',b⁆ := by
  let d := a * a'⁻¹
  have hd : d ∈ π.ker := by change π (a * a'⁻¹) = 1; simp [h]
  have hdc (x : E) : d * x = x * d :=
    (UniversalCentralExtension.central_iff π).mp hc d hd x
  have hdcomm : ⁅d,b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hdc b)
  calc
    ⁅a,b⁆ = ⁅d * a',b⁆ := by simp [d]
    _ = ⁅a',b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hdcomm, hdc]
      simp [mul_assoc]

theorem commutator_eq_of_projection_eq_right {a b b' : E} (h : π b = π b') :
    ⁅a,b⁆ = ⁅a,b'⁆ := by
  have hh := commutator_eq_of_projection_eq_left π hc (b := a) h
  simpa only [commutatorElement_inv] using congrArg Inv.inv hh

/-- The central part of the derived subgroup of a central extension. -/
def CentralDerivedKernel (π : E →* Q) (_hc : UniversalCentralExtension.Central π) :=
  (π.comp (commutator E).subtype).ker

instance : Group (CentralDerivedKernel π hc) := inferInstanceAs
  (Group (π.comp (commutator E).subtype).ker)

instance centralDerivedKernelCommGroup : CommGroup (CentralDerivedKernel π hc) where
  mul_comm x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (UniversalCentralExtension.central_iff π).mp hc x.1.1 x.2 y.1.1

variable (f : G →* Q) (g : H →* Q)
variable (hf : ∀ x y, Commute (f x) (g y))
variable (a : G → E) (b : H → E)
variable (ha : ∀ x, π (a x) = f x) (hb : ∀ y, π (b y) = g y)

def liftedCommutator (x : G) (y : H) : CentralDerivedKernel π hc :=
  ⟨⟨⁅a x,b y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩,
    by change π ⁅a x,b y⁆ = 1; rw [map_commutatorElement, ha, hb]; exact (hf x y).commutator_eq⟩

theorem liftedCommutator_mul_left (x x' : G) (y : H) :
    liftedCommutator π hc f g hf a b ha hb (x*x') y =
      liftedCommutator π hc f g hf a b ha hb x y *
        liftedCommutator π hc f g hf a b ha hb x' y := by
  apply Subtype.ext
  apply Subtype.ext
  change ⁅a (x*x'),b y⁆ = ⁅a x,b y⁆ * ⁅a x',b y⁆
  rw [commutator_eq_of_projection_eq_left π hc
    (show π (a (x*x')) = π (a x * a x') by simp [ha])]
  have hh : ⁅a x',b y⁆ ∈ π.ker := by
    change π ⁅a x',b y⁆ = 1
    rw [map_commutatorElement, ha, hb]
    exact (hf x' y).commutator_eq
  have hcomm := (UniversalCentralExtension.central_iff π).mp hc _ hh
  rw [commutatorElement_mul_left_eq_conj_mul, ← hcomm (a x)]
  simp only [mul_assoc, mul_inv_cancel_left]
  exact hcomm _

theorem liftedCommutator_mul_right (x : G) (y y' : H) :
    liftedCommutator π hc f g hf a b ha hb x (y*y') =
      liftedCommutator π hc f g hf a b ha hb x y *
        liftedCommutator π hc f g hf a b ha hb x y' := by
  apply Subtype.ext
  apply Subtype.ext
  change ⁅a x,b (y*y')⁆ = ⁅a x,b y⁆ * ⁅a x,b y'⁆
  rw [commutator_eq_of_projection_eq_right π hc
    (show π (b (y*y')) = π (b y * b y') by simp [hb])]
  have hh : ⁅a x,b y'⁆ ∈ π.ker := by
    change π ⁅a x,b y'⁆ = 1
    rw [map_commutatorElement, ha, hb]
    exact (hf x y').commutator_eq
  have hcomm := (UniversalCentralExtension.central_iff π).mp hc _ hh
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a x,b y⁆ * b y * ⁅a x,b y'⁆ * (b y)⁻¹ =
        ⁅a x,b y⁆ * (b y * ⁅a x,b y'⁆) * (b y)⁻¹ := by simp [mul_assoc]
    _ = ⁅a x,b y⁆ * ⁅a x,b y'⁆ := by rw [← hcomm]; simp [mul_assoc]

def liftedCommutatorHom : G →* H →* CentralDerivedKernel π hc :=
  MonoidHom.mk' (fun x ↦ MonoidHom.mk'
    (liftedCommutator π hc f g hf a b ha hb x)
    (liftedCommutator_mul_right π hc f g hf a b ha hb x)) (by
      intro x x'
      apply MonoidHom.ext
      intro y
      exact liftedCommutator_mul_left π hc f g hf a b ha hb x x' y)

omit hc
section BilinearDescent

variable {K : Type} [CommGroup K]

/-- A multiplicative pairing descends in its second argument. -/
def pairingRightAbelianization (c : G →* H →* K) : G →* Abelianization H →* K where
  toFun x := Abelianization.lift (c x)
  map_one' := by
    apply Abelianization.hom_ext
    ext y
    simp
  map_mul' x x' := by
    apply Abelianization.hom_ext
    ext y
    simp

/-- A multiplicative pairing into an abelian group descends through both
abelianizations. -/
def pairingAbelianization (c : G →* H →* K) :
    Abelianization G →* Abelianization H →* K :=
  Abelianization.lift (pairingRightAbelianization c)

@[simp] theorem pairingAbelianization_of (c : G →* H →* K) (x : G) (y : H) :
    pairingAbelianization c (Abelianization.of x) (Abelianization.of y) = c x y := rfl

def pairingAdditive (c : G →* H →* K) : H₁ G →+ H₁ H →+ Additive K where
  toFun x := (pairingAbelianization c x.toMul).toAdditive
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    change pairingAbelianization c 1 y.toMul = 1
    simp
  map_add' x x' := by
    apply AddMonoidHom.ext
    intro y
    change pairingAbelianization c (x.toMul * x'.toMul) y.toMul =
      pairingAbelianization c x.toMul y.toMul * pairingAbelianization c x'.toMul y.toMul
    simp

/-- The universal tensor map associated to a multiplicative pairing. -/
def pairingTensor (c : G →* H →* K) : TensorProduct ℤ (H₁ G) (H₁ H) →+ Additive K :=
  TensorProduct.liftAddHom (pairingAdditive c) (by
    intro n x y
    simp)

@[simp] theorem pairingTensor_of (c : G →* H →* K) (x : G) (y : H) :
    pairingTensor c (TensorProduct.tmul ℤ
      (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y))) =
        Additive.ofMul (c x y) := rfl

end BilinearDescent

end SmallPresentationStatements.Homology
