module

public import SmallPresentation.PackingCentralProduct
public import SmallPresentation.FreeAbelianProduct

/-! The global central relation kernel, with literal normalized row coordinates. -/
@[expose] public section

namespace SmallPresentationStatements.PackingBaseProduct

open Word

variable {L : ℕ} (Q : FP 2 L) {V C : Type} (π : V → C)
    [Fintype C] [DecidableEq C]

noncomputable def kernelAddEquiv : Additive (RelationExtension.Kernel (PackingBase.kernel Q π)) ≃+
    ∀ c, Additive (RelationExtension.Kernel (fiberKernel Q π c)) where
  toFun x c := Additive.ofMul (centralKernelProductEquiv Q π x.toMul c)
  invFun x := Additive.ofMul ((centralKernelProductEquiv Q π).symm (fun c ↦ (x c).toMul))
  left_inv x := (centralKernelProductEquiv Q π).symm_apply_apply x
  right_inv x := (centralKernelProductEquiv Q π).apply_symm_apply x
  map_add' x y := by
    funext c
    exact congrFun ((centralKernelProductEquiv Q π).map_mul x y) c

variable {d : C → ℕ} (e : ∀ c, Fiber π c ≃ Fin (d c))
    (hC : CentrallyClosed Q.Group) (hQ : Normalized Q) (hN : Noncyclic Q.Group)

noncomputable def globalBasisEquiv : FreeAbelianGroup (Σ c, SignedCoding.Relative.Row (d c)) ≃+
    Additive (RelationExtension.Kernel (PackingBase.kernel Q π)) :=
  (FreeAbelianProduct.sigmaEquiv _).trans
    ((AddEquiv.piCongrRight fun c ↦
      (SignedCoding.CentralComparison.basisEquiv Q hC hQ.commutator_eq_top hN).trans
        (fiberCentralKernelEquiv Q π c (e c)).symm.toAdditive).trans
      (kernelAddEquiv Q π).symm)

omit [Fintype C] [DecidableEq C] in
def normalizedIndex (j : Fin 2) : Fin L := ⟨j.val, lt_of_lt_of_le j.isLt hQ.1⟩

omit [Fintype C] [DecidableEq C] in
def fiberRowElement {c : C} (v w : Fiber π c) (hvw : v ≠ w) (i : Fin L) :
    RelationExtension.Kernel (fiberKernel Q π c) :=
  ⟨QuotientGroup.mk' (RelationExtension.commutatorKernel (fiberKernel Q π c)) (fiberRow Q π v w i), by
    change QuotientGroup.mk' (fiberKernel Q π c) (fiberRow Q π v w i) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨v,w,hvw,i,rfl⟩)⟩

omit [Fintype C] [DecidableEq C] in
def globalRowElement (v w : V) (hπ : π v = π w) (hvw : v ≠ w) (i : Fin L) :
    RelationExtension.Kernel (PackingBase.kernel Q π) :=
  ⟨QuotientGroup.mk' (RelationExtension.commutatorKernel (PackingBase.kernel Q π))
      (PackingBase.row Q π v w i), by
    change QuotientGroup.mk' (PackingBase.kernel Q π) (PackingBase.row Q π v w i) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨v,w,hπ,hvw,i,rfl⟩)⟩

theorem host_product_factor (c : C) (x : FreeGroup (Fiber π c)) :
    HostPartition.productEquiv π (HostPartition.factor π c x) = Pi.mulSingle c x := by
  apply (HostPartition.productEquiv π).symm.injective
  rw [MulEquiv.symm_apply_apply]
  change HostPartition.factor π c x = HostPartition.fromProduct π (Pi.mulSingle c x)
  simp only [HostPartition.fromProduct, MonoidHom.noncommPiCoprod_mulSingle]

theorem kernelProduct_globalRow {c : C} (v w : Fiber π c) (hvw : v ≠ w) (i : Fin L) :
    centralKernelProductEquiv Q π
      (globalRowElement Q π v.val w.val (v.property.trans w.property.symm)
        (fun h ↦ hvw (Subtype.ext h)) i) = Pi.mulSingle c (fiberRowElement Q π v w hvw i) := by
  funext c'
  apply Subtype.ext
  change centralProductEquiv Q π
    (QuotientGroup.mk' _ (PackingBase.row Q π v.val w.val i)) c' = _
  rw [centralProductEquiv_mk, ← factor_row Q π v w i, host_product_factor]
  by_cases h : c = c'
  · subst c'
    simp only [Pi.mulSingle_eq_same]
    rfl
  · simp [Pi.mulSingle_eq_of_ne (Ne.symm h)]

include hQ in
omit [Fintype C] [DecidableEq C] in
theorem fiberKernel_row_value (c : C) (a : SignedCoding.Relative.Pair (d c)) (i : Fin L) :
    (fiberCentralKernelEquiv Q π c (e c)
      (fiberRowElement Q π ((e c).symm a.val.1) ((e c).symm a.val.2)
        (fun h ↦ a.property ((e c).symm.injective h)) i)).val =
      (if i.val = 0 then SignedCoding.CentralComparison.defect Q hC a 0 else 1) *
      (if i.val = 1 then SignedCoding.CentralComparison.defect Q hC a 1 else 1) := by
  change QuotientGroup.mk' (RelationExtension.commutatorKernel (SignedCoding.relationSubgroup Q (d c))) ((FreeGroup.freeGroupCongr (e c)).toMonoidHom
    (fiberRow Q π ((e c).symm a.val.1) ((e c).symm a.val.2) i)) = _
  simp only [fiberRow, PackingBase.map_pair_eval]
  have hm (v : Fin (d c)) : (FreeGroup.freeGroupCongr (e c)).toMonoidHom
      (FreeGroup.of ((e c).symm v)) = FreeGroup.of v := by
    change FreeGroup.map (e c) (FreeGroup.of ((e c).symm v)) = _
    simp
  simp only [hm]
  have hcode (k : Fin 2) :
      eval ![QuotientGroup.mk' (RelationExtension.commutatorKernel (SignedCoding.relationSubgroup Q (d c)))
        (FreeGroup.of a.val.1), QuotientGroup.mk' _ (FreeGroup.of a.val.2)] (![code₁,code₂] k) =
      SignedCoding.centralCode Q a.val.1 a.val.2 k := by
    change eval ![SignedCoding.CentralComparison.originalVertex Q a.val.1,
      SignedCoding.CentralComparison.originalVertex Q a.val.2] (![code₁,code₂] k) = _
    have h := SignedCoding.eval_codeWord (SignedCoding.CentralComparison.originalVertex Q)
      a.val.1 a.val.2 k
    rw [← h]
    exact SignedCoding.CentralComparison.eval_originalVertex Q _
  have h0 := hcode 0
  have h1 := hcode 1
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
  rw [h0, h1]
  exact SignedCoding.CentralComparison.normalized_row_value Q hC hQ a i

omit [Fintype C] [DecidableEq C] in
theorem fiberKernel_normalizedRow (c : C) (a : SignedCoding.Relative.Pair (d c)) (j : Fin 2) :
    fiberCentralKernelEquiv Q π c (e c)
      (fiberRowElement Q π ((e c).symm a.val.1) ((e c).symm a.val.2)
        (fun h ↦ a.property ((e c).symm.injective h)) (normalizedIndex Q hQ j)) =
      SignedCoding.CentralComparison.defectElement Q hC a j := by
  apply Subtype.ext
  rw [fiberKernel_row_value Q π e hC hQ]
  fin_cases j <;> simp [normalizedIndex, SignedCoding.CentralComparison.defectElement]

include e hC hQ in
theorem globalRowElement_eq_one (v w : V) (hπ : π v = π w) (hvw : v ≠ w)
    (i : Fin L) (hi : 2 ≤ i.val) : globalRowElement Q π v w hπ hvw i = 1 := by
  let c := π v
  let v' : Fiber π c := ⟨v,rfl⟩
  let w' : Fiber π c := ⟨w,hπ.symm⟩
  have hvw' : v' ≠ w' := fun h ↦ hvw (congrArg Subtype.val h)
  have hz : fiberRowElement Q π v' w' hvw' i = 1 := by
    apply (fiberCentralKernelEquiv Q π c (e c)).injective
    rw [map_one]
    apply Subtype.ext
    let a : SignedCoding.Relative.Pair (d c) := ⟨(e c v',e c w'), fun h ↦ hvw' ((e c).injective h)⟩
    have h := fiberKernel_row_value Q π e hC hQ c a i
    simpa only [a, Equiv.symm_apply_apply, ite_eq_right (show i.val ≠ 0 by omega),
      ite_eq_right (show i.val ≠ 1 by omega), mul_one, Subgroup.coe_one] using h
  apply (centralKernelProductEquiv Q π).injective
  rw [map_one]
  have h := kernelProduct_globalRow Q π v' w' hvw' i
  simpa only [v',w', hz, Pi.mulSingle_one] using h

set_option backward.isDefEq.respectTransparency false in
theorem globalBasisEquiv_of (c : C) (a : SignedCoding.Relative.Pair (d c)) (j : Fin 2) :
    globalBasisEquiv Q π e hC hQ hN (FreeAbelianGroup.of ⟨c,(a,j)⟩) =
      Additive.ofMul (globalRowElement Q π ((e c).symm a.val.1).val ((e c).symm a.val.2).val
        (((e c).symm a.val.1).property.trans ((e c).symm a.val.2).property.symm)
        (fun h ↦ a.property ((e c).symm.injective (Subtype.ext h))) (normalizedIndex Q hQ j)) := by
  apply (kernelAddEquiv Q π).injective
  rw [globalBasisEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.apply_symm_apply,
    FreeAbelianProduct.sigmaEquiv_of]
  change (AddEquiv.piCongrRight fun c ↦
      (SignedCoding.CentralComparison.basisEquiv Q hC hQ.commutator_eq_top hN).trans
        (fiberCentralKernelEquiv Q π c (e c)).symm.toAdditive)
      (Pi.single c (FreeAbelianGroup.of (a,j))) =
    fun c' ↦ Additive.ofMul (centralKernelProductEquiv Q π _ c')
  simp only [toMul_ofMul]
  rw [kernelProduct_globalRow Q π ((e c).symm a.val.1) ((e c).symm a.val.2)
    (fun h ↦ a.property ((e c).symm.injective h)) (normalizedIndex Q hQ j)]
  funext c'
  by_cases hc : c = c'
  · subst c'
    simp only [AddEquiv.piCongrRight_apply, Pi.single_eq_same, Pi.mulSingle_eq_same,
      AddEquiv.trans_apply, SignedCoding.CentralComparison.basisEquiv_of]
    apply Additive.toMul.injective
    apply (fiberCentralKernelEquiv Q π c (e c)).injective
    change (fiberCentralKernelEquiv Q π c (e c))
      ((fiberCentralKernelEquiv Q π c (e c)).symm
        (SignedCoding.CentralComparison.defectElement Q hC a j)) =
      (fiberCentralKernelEquiv Q π c (e c))
        (fiberRowElement Q π ((e c).symm a.val.1) ((e c).symm a.val.2)
          (fun h ↦ a.property ((e c).symm.injective h)) (normalizedIndex Q hQ j))
    rw [MulEquiv.apply_symm_apply]
    exact (fiberKernel_normalizedRow Q π e hC hQ c a j).symm
  · simp [AddEquiv.piCongrRight_apply, Pi.single_eq_of_ne (Ne.symm hc),
      Pi.mulSingle_eq_of_ne (Ne.symm hc)]

abbrev BasisVertex (d : C → ℕ) := Σ c, SignedCoding.Relative.Pair (d c)

def basisTagEquiv : BasisVertex d ⊕ BasisVertex d ≃ (Σ c, SignedCoding.Relative.Row (d c)) where
  toFun
    | .inl a => ⟨a.1,(a.2,0)⟩
    | .inr a => ⟨a.1,(a.2,1)⟩
  invFun a := if a.2.2 = 0 then Sum.inl ⟨a.1,a.2.1⟩ else Sum.inr ⟨a.1,a.2.1⟩
  left_inv a := by cases a <;> simp
  right_inv a := by
    rcases a with ⟨c,a,j⟩
    fin_cases j <;> simp

noncomputable def sumBasisEquiv : FreeAbelianGroup (BasisVertex d ⊕ BasisVertex d) ≃+
    Additive (RelationExtension.Kernel (PackingBase.kernel Q π)) :=
  (FreeAbelianGroup.equivOfEquiv basisTagEquiv).trans (globalBasisEquiv Q π e hC hQ hN)

def pairVertex (v w : V) (hπ : π v = π w) (hvw : v ≠ w) : BasisVertex d :=
  ⟨π v, ⟨((e (π v)) ⟨v,rfl⟩, (e (π v)) ⟨w,hπ.symm⟩),
    fun h ↦ hvw (congrArg Subtype.val ((e (π v)).injective h))⟩⟩

theorem sumBasisEquiv_of_left (v w : V) (hπ : π v = π w) (hvw : v ≠ w) :
    sumBasisEquiv Q π e hC hQ hN (FreeAbelianGroup.of (Sum.inl (pairVertex π e v w hπ hvw))) =
      Additive.ofMul (globalRowElement Q π v w hπ hvw (normalizedIndex Q hQ 0)) := by
  change globalBasisEquiv Q π e hC hQ hN
    (FreeAbelianGroup.of ⟨π v,((pairVertex π e v w hπ hvw).2,0)⟩) = _
  simp only [pairVertex]
  rw [globalBasisEquiv_of]
  simp only [Equiv.symm_apply_apply]

theorem sumBasisEquiv_of_right (v w : V) (hπ : π v = π w) (hvw : v ≠ w) :
    sumBasisEquiv Q π e hC hQ hN (FreeAbelianGroup.of (Sum.inr (pairVertex π e v w hπ hvw))) =
      Additive.ofMul (globalRowElement Q π v w hπ hvw (normalizedIndex Q hQ 1)) := by
  change globalBasisEquiv Q π e hC hQ hN
    (FreeAbelianGroup.of ⟨π v,((pairVertex π e v w hπ hvw).2,1)⟩) = _
  simp only [pairVertex]
  rw [globalBasisEquiv_of]
  simp only [Equiv.symm_apply_apply]

end SmallPresentationStatements.PackingBaseProduct
