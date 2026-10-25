module

public import SmallPresentation.KunnethModel

/-! The integral degree-two product formula, proved directly from the Hopf
model using the bilinear central extension. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G H : Type) [Group G] [Group H]

abbrev ProductModelKernel := CentralDerivedKernel
  (productModelProjection G H) (productModelProjection_central G H)

def productKernelComparison : Schur (G × H) ≃* ProductModelKernel G H where
  toFun x := ⟨⟨toProductModel G H x.1.1,hom_mem_commutator _ x.1.2⟩,by
    change productModelProjection G H (toProductModel G H x.1.1) = 1
    rw [← MonoidHom.comp_apply, toProductModel_projection]
    exact (totalEvaluation_eq_one_iff (G × H) _).mpr x.2⟩
  invFun x := ⟨⟨fromProductModel G H x.1.1,hom_mem_commutator _ x.1.2⟩,by
    apply (totalEvaluation_eq_one_iff (G × H) _).mp
    change totalEvaluation (G × H) (fromProductModel G H x.1.1) = 1
    rw [← MonoidHom.comp_apply, fromProductModel_projection]
    exact x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact from_toProductModel G H x.1.1 x.1.2
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact to_fromProductModel G H x.1.1 x.1.2
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul _ _ _

def productKernelLeft (x : ProductModelKernel G H) : Schur G :=
  ⟨⟨x.1.1.left,hom_mem_commutator (BilinearExtension.fst _) x.1.2⟩,
    (totalEvaluation_eq_one_iff G _).mp (congrArg Prod.fst x.2)⟩

def productKernelRight (x : ProductModelKernel G H) : Schur H :=
  ⟨⟨x.1.1.right,hom_mem_commutator (BilinearExtension.snd _) x.1.2⟩,
    (totalEvaluation_eq_one_iff H _).mp (congrArg Prod.snd x.2)⟩

def productKernelOfCoordinates (x : Schur G) (y : Schur H) (t : ProductTensor G H) :
    ProductModelKernel G H :=
  ⟨⟨⟨x.1.1,y.1.1,t⟩,by
    rw [← BilinearExtension.decompose (totalTensorPairing G H)
      (⟨x.1.1,y.1.1,t⟩ : ProductCentralModel G H)]
    exact (commutator _).mul_mem
      ((commutator _).mul_mem (hom_mem_commutator (BilinearExtension.inl _) x.1.2)
        (hom_mem_commutator (BilinearExtension.inr _) y.1.2))
      (productModel_center_mem_commutator G H t)⟩,by
      apply Prod.ext
      · exact (totalEvaluation_eq_one_iff G _).mpr x.2
      · exact (totalEvaluation_eq_one_iff H _).mpr y.2⟩

def productKernelCoordinates : ProductModelKernel G H ≃*
    Schur G × Schur H × Multiplicative (ProductTensor G H) where
  toFun x := (productKernelLeft G H x,productKernelRight G H x,
    Multiplicative.ofAdd x.1.1.central)
  invFun x := productKernelOfCoordinates G H x.1 x.2.1 x.2.2.toAdd
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change Multiplicative.ofAdd
          (x.1.1.central+y.1.1.central-
            BilinearExtension.pairing (totalTensorPairing G H) y.1.1.left x.1.1.right) =
          Multiplicative.ofAdd (x.1.1.central+y.1.1.central)
        have hy : totalEvaluation G y.1.1.left = 1 := congrArg Prod.fst y.2
        rw [model_pairing_left_zero G H hy, sub_zero]

/-- The Schur multiplier of an arbitrary product, with its concrete mixed
commutator tensor summand. No Künneth theorem is assumed in this proof. -/
def schurProductEquiv : Schur (G × H) ≃*
    Schur G × Schur H × Multiplicative (ProductTensor G H) :=
  (productKernelComparison G H).trans (productKernelCoordinates G H)

/-- Integral degree-two Künneth for arbitrary groups, in the canonical Hopf model. -/
def kunnethEquiv : H₂ (G × H) ≃+ H₂ G × H₂ H × ProductTensor G H where
  toFun x := (Additive.ofMul (schurProductEquiv G H x.toMul).1,
    Additive.ofMul (schurProductEquiv G H x.toMul).2.1,
    (schurProductEquiv G H x.toMul).2.2.toAdd)
  invFun x := Additive.ofMul ((schurProductEquiv G H).symm
    (x.1.toMul,x.2.1.toMul,Multiplicative.ofAdd x.2.2))
  left_inv x := (schurProductEquiv G H).symm_apply_apply x
  right_inv x := (schurProductEquiv G H).apply_symm_apply
    (x.1.toMul,x.2.1.toMul,Multiplicative.ofAdd x.2.2)
  map_add' x y := (schurProductEquiv G H).map_mul x y

end SmallPresentationStatements.Homology
