module

public import SmallPresentation.CentralProduct
public import SmallPresentation.PackingBaseProduct
public import SmallPresentation.SignedRelationBasis

/-! Centralizing all signed rows in the partition product is a product of
the centralizations of the rows in each fiber. -/
@[expose] public section

namespace SmallPresentationStatements.PackingBaseProduct

variable {L : ℕ} (Q : FP 2 L) {V C : Type} (π : V → C)

abbrev fiberKernel (c : C) := Subgroup.normalClosure (fiberRelators Q π c)

variable [Fintype C] [DecidableEq C]

theorem toProductPre_ker : (toProductPre Q π).ker = PackingBase.kernel Q π := by
  ext x
  change productEquiv Q π (PackingBase.quotient Q π x) = 1 ↔ x ∈ PackingBase.kernel Q π
  rw [← (productEquiv Q π).map_one, (productEquiv Q π).injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem kernel_map_product : (PackingBase.kernel Q π).map (HostPartition.productEquiv π).toMonoidHom =
    Subgroup.pi Set.univ (fiberKernel Q π) := by
  rw [← toProductPre_ker]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change toProductPre Q π y = 1 at hy
    intro c hc
    exact (QuotientGroup.eq_one_iff _).mp (congrFun hy c)
  · intro hx
    refine ⟨(HostPartition.productEquiv π).symm x, ?_, (HostPartition.productEquiv π).apply_symm_apply x⟩
    change toProductPre Q π ((HostPartition.productEquiv π).symm x) = 1
    change quotientFactors Q π ((HostPartition.productEquiv π) ((HostPartition.productEquiv π).symm x)) = 1
    rw [MulEquiv.apply_symm_apply]
    funext c
    exact (QuotientGroup.eq_one_iff _).mpr (hx c (Set.mem_univ c))

noncomputable def centralProductEquiv : RelationExtension.Total (PackingBase.kernel Q π) ≃*
    ∀ c, RelationExtension.Total (fiberKernel Q π c) :=
  (CentralRelationMap.congr _ _ (HostPartition.productEquiv π) (kernel_map_product Q π)).trans
    (CentralProduct.totalEquiv (fun c ↦ FreeGroup (Fiber π c)) (fiberKernel Q π))

@[simp] theorem centralProductEquiv_mk (x : HostPartition.Group π) :
    centralProductEquiv Q π (QuotientGroup.mk' (RelationExtension.commutatorKernel (PackingBase.kernel Q π)) x) =
      fun c ↦ QuotientGroup.mk' (RelationExtension.commutatorKernel (fiberKernel Q π c))
        (HostPartition.productEquiv π x c) := by
  simp only [centralProductEquiv, MulEquiv.trans_apply, CentralRelationMap.congr_mk,
    CentralProduct.totalEquiv_mk]

noncomputable def centralKernelProductEquiv : RelationExtension.Kernel (PackingBase.kernel Q π) ≃*
    ∀ c, RelationExtension.Kernel (fiberKernel Q π c) :=
  (CentralRelationMap.kernelCongr _ _ (HostPartition.productEquiv π) (kernel_map_product Q π)).trans
    (CentralProduct.kernelEquiv (fun c ↦ FreeGroup (Fiber π c)) (fiberKernel Q π))

omit [Fintype C] [DecidableEq C] in
theorem fiberCode_projects {d : ℕ} (c : C) (e : Fiber π c ≃ Fin d)
    (x : FreeGroup (Fiber π c)) :
    PresentedGroup.mk (SignedCoding.relators Q d) (FreeGroup.freeGroupCongr e x) =
      fiberCodeEquiv Q π c e (PresentedGroup.mk (fiberRelators Q π c) x) := by
  have h : (PresentedGroup.mk (SignedCoding.relators Q d)).comp (FreeGroup.freeGroupCongr e).toMonoidHom =
      (fiberCodeEquiv Q π c e).toMonoidHom.comp (PresentedGroup.mk (fiberRelators Q π c)) := by
    apply FreeGroup.ext_hom
    intro v
    change PresentedGroup.of (e v) = fiberToCode Q π c e (PresentedGroup.of v)
    exact (fiberToCode_of Q π c e v).symm
  exact DFunLike.congr_fun h x

omit [Fintype C] [DecidableEq C] in
theorem fiberKernel_map {d : ℕ} (c : C) (e : Fiber π c ≃ Fin d) :
    (fiberKernel Q π c).map (FreeGroup.freeGroupCongr e).toMonoidHom = SignedCoding.relationSubgroup Q d := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change PresentedGroup.mk (SignedCoding.relators Q d) (FreeGroup.freeGroupCongr e y) = 1
    rw [fiberCode_projects]
    rw [show PresentedGroup.mk (fiberRelators Q π c) y = 1 from (QuotientGroup.eq_one_iff y).mpr hy,
      map_one]
  · intro hx
    refine ⟨(FreeGroup.freeGroupCongr e).symm x, ?_, (FreeGroup.freeGroupCongr e).apply_symm_apply x⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change PresentedGroup.mk (fiberRelators Q π c) ((FreeGroup.freeGroupCongr e).symm x) = 1
    apply (fiberCodeEquiv Q π c e).injective
    rw [map_one, ← fiberCode_projects, MulEquiv.apply_symm_apply]
    exact (QuotientGroup.eq_one_iff x).mpr hx

omit [Fintype C] [DecidableEq C] in
noncomputable def fiberCentralEquiv {d : ℕ} (c : C) (e : Fiber π c ≃ Fin d) :
    RelationExtension.Total (fiberKernel Q π c) ≃* SignedCoding.CentralGroup Q d :=
  CentralRelationMap.congr _ _ (FreeGroup.freeGroupCongr e) (fiberKernel_map Q π c e)

omit [Fintype C] [DecidableEq C] in
noncomputable def fiberCentralKernelEquiv {d : ℕ} (c : C) (e : Fiber π c ≃ Fin d) :
    RelationExtension.Kernel (fiberKernel Q π c) ≃*
      RelationExtension.Kernel (SignedCoding.relationSubgroup Q d) :=
  CentralRelationMap.kernelCongr _ _ (FreeGroup.freeGroupCongr e) (fiberKernel_map Q π c e)

end SmallPresentationStatements.PackingBaseProduct
