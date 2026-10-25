module

public import SmallPresentation.KunnethEquivalence
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-! Canonical maps in the integral degree-two Künneth formula. The square
formula used for mitosis is a corollary of the arbitrary-product equivalence. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable (G H : Type) [Group G] [Group H]

theorem toProductModel_left (x : CanonicalTotal (G × H))
    (hx : x ∈ commutator (CanonicalTotal (G × H))) :
    (toProductModel G H x).left = canonicalTotalMap (MonoidHom.fst G H) x := by
  apply central_lifts_agree_on_commutator (totalEvaluation G) (totalEvaluation_central G)
    ((BilinearExtension.fst _).comp (toProductModel G H))
    (canonicalTotalMap (MonoidHom.fst G H))
  · apply MonoidHom.ext
    intro z
    change totalEvaluation G (toProductModel G H z).left =
      totalEvaluation G (canonicalTotalMap (MonoidHom.fst G H) z)
    rw [canonicalTotalMap_projection]
    exact congrArg Prod.fst (DFunLike.congr_fun (toProductModel_projection G H) z)
  · exact hx

theorem toProductModel_right (x : CanonicalTotal (G × H))
    (hx : x ∈ commutator (CanonicalTotal (G × H))) :
    (toProductModel G H x).right = canonicalTotalMap (MonoidHom.snd G H) x := by
  apply central_lifts_agree_on_commutator (totalEvaluation H) (totalEvaluation_central H)
    ((BilinearExtension.snd _).comp (toProductModel G H))
    (canonicalTotalMap (MonoidHom.snd G H))
  · apply MonoidHom.ext
    intro z
    change totalEvaluation H (toProductModel G H z).right =
      totalEvaluation H (canonicalTotalMap (MonoidHom.snd G H) z)
    rw [canonicalTotalMap_projection]
    exact congrArg Prod.snd (DFunLike.congr_fun (toProductModel_projection G H) z)
  · exact hx

@[simp] theorem kunnethEquiv_fst (x : H₂ (G × H)) :
    (kunnethEquiv G H x).1 = map₂ (MonoidHom.fst G H) x := by
  apply Subtype.ext
  apply Subtype.ext
  exact toProductModel_left G H x.toMul.1.1 x.toMul.1.2

@[simp] theorem kunnethEquiv_snd (x : H₂ (G × H)) :
    (kunnethEquiv G H x).2.1 = map₂ (MonoidHom.snd G H) x := by
  apply Subtype.ext
  apply Subtype.ext
  exact toProductModel_right G H x.toMul.1.1 x.toMul.1.2

theorem toProductModel_inl (x : CanonicalTotal G) (hx : x ∈ commutator (CanonicalTotal G)) :
    toProductModel G H (canonicalTotalMap (MonoidHom.inl G H) x) =
      BilinearExtension.inl (totalTensorPairing G H) x := by
  apply central_lifts_agree_on_commutator (productModelProjection G H)
    (productModelProjection_central G H)
    ((toProductModel G H).comp (canonicalTotalMap (MonoidHom.inl G H)))
    (BilinearExtension.inl _)
  · apply MonoidHom.ext
    intro z
    change productModelProjection G H
      (toProductModel G H (canonicalTotalMap (MonoidHom.inl G H) z)) = _
    rw [← MonoidHom.comp_apply, toProductModel_projection, canonicalTotalMap_projection]
    simp
  · exact hx

theorem toProductModel_inr (x : CanonicalTotal H) (hx : x ∈ commutator (CanonicalTotal H)) :
    toProductModel G H (canonicalTotalMap (MonoidHom.inr G H) x) =
      BilinearExtension.inr (totalTensorPairing G H) x := by
  apply central_lifts_agree_on_commutator (productModelProjection G H)
    (productModelProjection_central G H)
    ((toProductModel G H).comp (canonicalTotalMap (MonoidHom.inr G H)))
    (BilinearExtension.inr _)
  · apply MonoidHom.ext
    intro z
    change productModelProjection G H
      (toProductModel G H (canonicalTotalMap (MonoidHom.inr G H) z)) = _
    rw [← MonoidHom.comp_apply, toProductModel_projection, canonicalTotalMap_projection]
    simp
  · exact hx

@[simp] theorem kunnethEquiv_inl (x : H₂ G) :
    kunnethEquiv G H (map₂ (MonoidHom.inl G H) x) = (x,0,0) := by
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simp
    · change (toProductModel G H
        (canonicalTotalMap (MonoidHom.inl G H) x.toMul.1.1)).central = 0
      rw [toProductModel_inl G H _ x.toMul.1.2]
      rfl

@[simp] theorem kunnethEquiv_inr (x : H₂ H) :
    kunnethEquiv G H (map₂ (MonoidHom.inr G H) x) = (0,x,0) := by
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simp
    · change (toProductModel G H
        (canonicalTotalMap (MonoidHom.inr G H) x.toMul.1.1)).central = 0
      rw [toProductModel_inr G H _ x.toMul.1.2]
      rfl

theorem toProductModel_tensor (t : ProductTensor G H) :
    toProductModel G H (tensorCommutatorTotal G H (Multiplicative.ofAdd t)) =
      BilinearExtension.center (totalTensorPairing G H) (Multiplicative.ofAdd t) := by
  have h := to_fromProductModel G H _ (productModel_center_mem_commutator G H t)
  simpa only [fromProductModel, BilinearExtension.lift_center] using h

@[simp] theorem kunnethEquiv_tensor (t : ProductTensor G H) :
    kunnethEquiv G H (tensorCommutator G H t) = (0,0,t) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    change (toProductModel G H (tensorCommutatorTotal G H (Multiplicative.ofAdd t))).left = 1
    rw [toProductModel_tensor]
    rfl
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change (toProductModel G H (tensorCommutatorTotal G H (Multiplicative.ofAdd t))).right = 1
      rw [toProductModel_tensor]
      rfl
    · change (toProductModel G H (tensorCommutatorTotal G H (Multiplicative.ofAdd t))).central = t
      rw [toProductModel_tensor]
      rfl

/-- The reduced diagonal is retained as the actual tensor component, with no
assumption that it vanishes. -/
def reducedDiagonal (J : Type) [Group J] : H₂ J →+ ProductTensor J J :=
  (AddMonoidHom.snd (H₂ J) (ProductTensor J J)).comp
    ((AddMonoidHom.snd (H₂ J) (H₂ J × ProductTensor J J)).comp
      ((kunnethEquiv J J).toAddMonoidHom.comp
        (map₂ ((MonoidHom.id J).prod (MonoidHom.id J)))))

@[simp] theorem kunnethEquiv_diagonal (J : Type) [Group J] (x : H₂ J) :
    kunnethEquiv J J (map₂ ((MonoidHom.id J).prod (MonoidHom.id J)) x) =
      (x,x,reducedDiagonal J x) := by
  apply Prod.ext
  · simp
  · apply Prod.ext
    · simp
    · rfl

/-- The square version used by finite mitosis, now a proved specialization. -/
theorem kunneth_square (J : Type) [Group J] :
    ∃ (e : H₂ (J × J) ≃+ H₂ J × H₂ J × TensorProduct ℤ (H₁ J) (H₁ J))
      (δ : H₂ J →+ TensorProduct ℤ (H₁ J) (H₁ J)),
      (∀ b, e (map₂ (MonoidHom.inl J J) b) = (b,0,0)) ∧
      (∀ b, e (map₂ (MonoidHom.inr J J) b) = (0,b,0)) ∧
      (∀ b, e (map₂ ((MonoidHom.id J).prod (MonoidHom.id J)) b) = (b,b,δ b)) :=
  ⟨kunnethEquiv J J,reducedDiagonal J,kunnethEquiv_inl J J,kunnethEquiv_inr J J,
    kunnethEquiv_diagonal J⟩

@[simp] theorem kunnethEquiv_symm_apply (a : H₂ G) (b : H₂ H) (t : ProductTensor G H) :
    (kunnethEquiv G H).symm (a,b,t) = map₂ (MonoidHom.inl G H) a +
      map₂ (MonoidHom.inr G H) b + tensorCommutator G H t := by
  apply (kunnethEquiv G H).injective
  simp

variable {G H} {G' H' : Type} [Group G'] [Group H']

/-- The mixed tensor class is natural in both groups. -/
theorem tensorCommutator_natural (f : G →* G') (g : H →* H') (t : ProductTensor G H) :
    map₂ (f.prodMap g) (tensorCommutator G H t) =
      tensorCommutator G' H' (TensorProduct.map (map₁ f).toIntLinearMap
        (map₁ g).toIntLinearMap t) := by
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, ht, ht']
  | tmul a b =>
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (commutator G) a.toMul
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (commutator H) b.toMul
    apply Subtype.ext
    apply Subtype.ext
    change canonicalTotalMap (f.prodMap g)
      ⁅totalGenerator (G × H) (x,1),totalGenerator (G × H) (1,y)⁆ =
      ⁅totalGenerator (G' × H') (f x,1),totalGenerator (G' × H') (1,g y)⁆
    simp [map_commutatorElement]

/-- Naturality of the full integral degree-two Künneth equivalence. -/
theorem kunnethEquiv_natural (f : G →* G') (g : H →* H') (x : H₂ (G × H)) :
    kunnethEquiv G' H' (map₂ (f.prodMap g) x) =
      (map₂ f (kunnethEquiv G H x).1,
        map₂ g (kunnethEquiv G H x).2.1,
        TensorProduct.map (map₁ f).toIntLinearMap (map₁ g).toIntLinearMap
          (kunnethEquiv G H x).2.2) := by
  obtain ⟨⟨a,b,t⟩,rfl⟩ := (kunnethEquiv G H).symm.surjective x
  have hl : map₂ (f.prodMap g) (map₂ (MonoidHom.inl G H) a) =
      map₂ (MonoidHom.inl G' H') (map₂ f a) := by
    rw [map₂_comp, map₂_comp]
    have heq : (f.prodMap g).comp (MonoidHom.inl G H) =
        (MonoidHom.inl G' H').comp f := by ext z <;> simp
    rw [heq]
  have hr : map₂ (f.prodMap g) (map₂ (MonoidHom.inr G H) b) =
      map₂ (MonoidHom.inr G' H') (map₂ g b) := by
    rw [map₂_comp, map₂_comp]
    have heq : (f.prodMap g).comp (MonoidHom.inr G H) =
        (MonoidHom.inr G' H').comp g := by ext z <;> simp
    rw [heq]
  rw [AddEquiv.apply_symm_apply, kunnethEquiv_symm_apply]
  simp only [map_add, hl, hr, tensorCommutator_natural, kunnethEquiv_inl,
    kunnethEquiv_inr, kunnethEquiv_tensor, Prod.mk_add_mk,
    add_zero, zero_add]

end SmallPresentationStatements.Homology
