module

public import SmallPresentation.KunnethTensor

/-! A central extension detecting all three summands of the Schur multiplier
of an arbitrary direct product. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable (G H : Type) [Group G] [Group H]

abbrev ProductCentralModel := BilinearExtension (totalTensorPairing G H)

def productModelProjection : ProductCentralModel G H →* G × H :=
  ((totalEvaluation G).comp (BilinearExtension.fst _)).prod
    ((totalEvaluation H).comp (BilinearExtension.snd _))

@[simp] theorem productModelProjection_apply (x : ProductCentralModel G H) :
    productModelProjection G H x = (totalEvaluation G x.left,totalEvaluation H x.right) := rfl

@[simp] theorem model_pairing_left_zero {x : CanonicalTotal G} (hx : totalEvaluation G x = 1)
    (y : CanonicalTotal H) : BilinearExtension.pairing (totalTensorPairing G H) x y = 0 := by
  simp [BilinearExtension.pairing, hx]

@[simp] theorem model_pairing_right_zero (x : CanonicalTotal G) {y : CanonicalTotal H}
    (hy : totalEvaluation H y = 1) :
    BilinearExtension.pairing (totalTensorPairing G H) x y = 0 := by
  simp [BilinearExtension.pairing, hy]

theorem productModelProjection_central : UniversalCentralExtension.Central
    (productModelProjection G H) := by
  apply (UniversalCentralExtension.central_iff _).mpr
  intro z hz x
  have hzG : totalEvaluation G z.left = 1 := congrArg Prod.fst hz
  have hzH : totalEvaluation H z.right = 1 := congrArg Prod.snd hz
  apply BilinearExtension.ext
  · exact (UniversalCentralExtension.central_iff _).mp (totalEvaluation_central G) _ hzG _
  · exact (UniversalCentralExtension.central_iff _).mp (totalEvaluation_central H) _ hzH _
  · simp [hzG,hzH,add_comm]

def productModelSection (x : G × H) : ProductCentralModel G H :=
  BilinearExtension.inl _ (totalGenerator G x.1) *
    BilinearExtension.inr _ (totalGenerator H x.2)

@[simp] theorem productModelSection_projection (x : G × H) :
    productModelProjection G H (productModelSection G H x) = x := by
  ext <;> simp [productModelSection]

def toProductModel : CanonicalTotal (G × H) →* ProductCentralModel G H :=
  canonicalTotalLift (productModelProjection G H) (productModelProjection_central G H)
    (productModelSection G H) (productModelSection_projection G H)

@[simp] theorem toProductModel_generator (x : G × H) :
    toProductModel G H (totalGenerator (G × H) x) = productModelSection G H x :=
  canonicalTotalLift_generator _ _ _ _ _

theorem toProductModel_projection :
    (productModelProjection G H).comp (toProductModel G H) = totalEvaluation (G × H) :=
  canonicalTotalLift_projection _ _ _ _

def fromProductModel : ProductCentralModel G H →* CanonicalTotal (G × H) :=
  BilinearExtension.lift (totalTensorPairing G H)
    (canonicalTotalMap (MonoidHom.inl G H)) (canonicalTotalMap (MonoidHom.inr G H))
    (tensorCommutatorTotal G H) (tensorCommutatorTotal_central G H)
    (tensorCommutatorTotal_totalPairing G H)

theorem fromProductModel_projection :
    (totalEvaluation (G × H)).comp (fromProductModel G H) = productModelProjection G H := by
  apply MonoidHom.ext
  intro x
  change totalEvaluation (G × H) (canonicalTotalMap (MonoidHom.inl G H) x.left *
    canonicalTotalMap (MonoidHom.inr G H) x.right *
    tensorCommutatorTotal G H (Multiplicative.ofAdd x.central)) = _
  simp [canonicalTotalMap_projection]

theorem from_toProductModel (x : CanonicalTotal (G × H))
    (hx : x ∈ commutator (CanonicalTotal (G × H))) :
    fromProductModel G H (toProductModel G H x) = x := by
  apply central_lifts_agree_on_commutator (totalEvaluation (G × H))
    (totalEvaluation_central (G × H)) ((fromProductModel G H).comp (toProductModel G H))
    (MonoidHom.id _)
  · rw [← MonoidHom.comp_assoc, fromProductModel_projection, toProductModel_projection,
      MonoidHom.comp_id]
  · exact hx

theorem to_fromProductModel (x : ProductCentralModel G H)
    (hx : x ∈ commutator (ProductCentralModel G H)) :
    toProductModel G H (fromProductModel G H x) = x := by
  apply central_lifts_agree_on_commutator (productModelProjection G H)
    (productModelProjection_central G H) ((toProductModel G H).comp (fromProductModel G H))
    (MonoidHom.id _)
  · rw [← MonoidHom.comp_assoc, toProductModel_projection, fromProductModel_projection,
      MonoidHom.comp_id]
  · exact hx

theorem hom_mem_commutator {A B : Type} [Group A] [Group B] (f : A →* B)
    {x : A} (hx : x ∈ commutator A) : f x ∈ commutator B := by
  have h : (commutator A).map f ≤ commutator B := by
    rw [map_commutator_eq]
    exact Subgroup.commutator_mono le_top le_top
  exact h ⟨x,hx,rfl⟩

theorem productModel_center_mem_commutator (t : ProductTensor G H) :
    BilinearExtension.center (totalTensorPairing G H) (Multiplicative.ofAdd t) ∈
      commutator (ProductCentralModel G H) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' =>
    change BilinearExtension.center _ (Multiplicative.ofAdd t * Multiplicative.ofAdd t') ∈ _
    rw [map_mul]
    exact (commutator _).mul_mem ht ht'
  | tmul a b =>
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) a.toMul
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (commutator H) b.toMul
    change BilinearExtension.center _ (tensorPairing G H g h) ∈ _
    have heq : tensorPairing G H g h =
        totalTensorPairing G H (totalGenerator G g) (totalGenerator H h) := by simp
    rw [heq, ← BilinearExtension.commutator_inl_inr]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end SmallPresentationStatements.Homology
