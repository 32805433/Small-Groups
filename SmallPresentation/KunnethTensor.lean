module

public import SmallPresentation.KunnethTotal
public import SmallPresentation.KunnethCentralProduct

/-! The canonical mixed-commutator map from the tensor product of two
abelianizations to the Schur multiplier of their product. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable (G H : Type) [Group G] [Group H]

abbrev ProductTensor := TensorProduct ℤ (H₁ G) (H₁ H)

def tensorPairing : G →* H →* Multiplicative (ProductTensor G H) where
  toFun x :=
    { toFun := fun y ↦ Multiplicative.ofAdd (TensorProduct.tmul ℤ
        (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)))
      map_one' := by simp
      map_mul' y y' := by simp [TensorProduct.tmul_add] }
  map_one' := by ext y; simp
  map_mul' x x' := by ext y; simp [TensorProduct.add_tmul]

def productLiftedPairing : G →* H →*
    CentralDerivedKernel (totalEvaluation (G × H)) (totalEvaluation_central (G × H)) :=
  liftedCommutatorHom (totalEvaluation (G × H)) (totalEvaluation_central (G × H))
    (MonoidHom.inl G H) (MonoidHom.inr G H) (fun x y ↦ MonoidHom.commute_inl_inr x y)
    (fun x ↦ totalGenerator (G × H) (x,1)) (fun y ↦ totalGenerator (G × H) (1,y))
    (fun _x ↦ totalEvaluation_generator _ _) (fun _y ↦ totalEvaluation_generator _ _)

/-- The mixed tensor class is represented by a commutator of canonical lifts. -/
def tensorCommutator : ProductTensor G H →+ H₂ (G × H) :=
  (centralDerivedKernelEquiv (G × H)).toMonoidHom.toAdditive.comp
    (pairingTensor (productLiftedPairing G H))

def tensorCommutatorTotal : Multiplicative (ProductTensor G H) →* CanonicalTotal (G × H) :=
  (commutator (CanonicalTotal (G × H))).subtype.comp
    ((Schur (G × H)).subtype.comp (tensorCommutator G H).toMultiplicative)

@[simp] theorem tensorCommutatorTotal_pairing (x : G) (y : H) :
    tensorCommutatorTotal G H (tensorPairing G H x y) =
      ⁅totalGenerator (G × H) (x,1),totalGenerator (G × H) (1,y)⁆ := rfl

theorem tensorCommutatorTotal_central (t : Multiplicative (ProductTensor G H))
    (x : CanonicalTotal (G × H)) : Commute (tensorCommutatorTotal G H t) x := by
  exact RelationExtension.kernel_central (canonicalRelations (G × H)) _
    ((tensorCommutator G H t.toAdd).toMul.property) x

@[simp] theorem tensorCommutatorTotal_evaluation (t : Multiplicative (ProductTensor G H)) :
    totalEvaluation (G × H) (tensorCommutatorTotal G H t) = 1 :=
  (totalEvaluation_eq_one_iff (G × H) _).mpr (tensorCommutator G H t.toAdd).toMul.property

def totalTensorPairing : CanonicalTotal G →* CanonicalTotal H →*
    Multiplicative (ProductTensor G H) where
  toFun x := (tensorPairing G H (totalEvaluation G x)).comp (totalEvaluation H)
  map_one' := by ext y; simp
  map_mul' x x' := by ext y; simp

@[simp] theorem totalTensorPairing_apply (x : CanonicalTotal G) (y : CanonicalTotal H) :
    totalTensorPairing G H x y = tensorPairing G H (totalEvaluation G x) (totalEvaluation H y) := rfl

theorem tensorCommutatorTotal_totalPairing (x : CanonicalTotal G) (y : CanonicalTotal H) :
    tensorCommutatorTotal G H (totalTensorPairing G H x y) =
      ⁅canonicalTotalMap (MonoidHom.inl G H) x,canonicalTotalMap (MonoidHom.inr G H) y⁆ := by
  rw [totalTensorPairing_apply, tensorCommutatorTotal_pairing]
  rw [commutator_eq_of_projection_eq_left (totalEvaluation (G × H))
    (totalEvaluation_central (G × H)) (a' := canonicalTotalMap (MonoidHom.inl G H) x)
    (by simp [canonicalTotalMap_projection])]
  exact commutator_eq_of_projection_eq_right (totalEvaluation (G × H))
    (totalEvaluation_central (G × H)) (by simp [canonicalTotalMap_projection])

end SmallPresentationStatements.Homology
