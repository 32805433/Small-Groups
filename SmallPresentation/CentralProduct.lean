module

public import SmallPresentation.RelativeRelationModule
public import Mathlib.GroupTheory.Commutator.Finite

/-! Central relation extensions commute with finite direct products. -/
@[expose] public section

namespace SmallPresentationStatements.CentralProduct

open scoped commutatorElement

variable {C : Type} (G : C → Type) [∀ c, Group (G c)] (N : ∀ c, Subgroup (G c))
    [∀ c, (N c).Normal]

instance piNormal : (Subgroup.pi Set.univ N).Normal where
  conj_mem := by
    intro x hx g c hc
    exact Subgroup.Normal.conj_mem inferInstance (x c) (hx c hc) (g c)

def quotientMap : (∀ c, G c) →* ∀ c, G c ⧸ N c :=
  MonoidHom.pi (fun c ↦ (QuotientGroup.mk' (N c)).comp (Pi.evalMonoidHom G c))

theorem quotientMap_ker : (quotientMap G N).ker = Subgroup.pi Set.univ N := by
  ext x
  change (fun c ↦ QuotientGroup.mk' (N c) (x c)) = 1 ↔ ∀ c, c ∈ Set.univ → x c ∈ N c
  rw [funext_iff]
  simp only [Set.mem_univ, forall_true_left, Pi.one_apply]
  exact forall_congr' fun c ↦ QuotientGroup.eq_one_iff (x c)

theorem quotientMap_surjective : Function.Surjective (quotientMap G N) := by
  intro x
  choose y hy using fun c ↦ QuotientGroup.mk'_surjective (N c) (x c)
  exact ⟨y, funext hy⟩

noncomputable def quotientEquiv : ((∀ c, G c) ⧸ Subgroup.pi Set.univ N) ≃* ∀ c, G c ⧸ N c :=
  (QuotientGroup.quotientMulEquivOfEq (quotientMap_ker G N).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quotientMap G N) (quotientMap_surjective G N))

@[simp] theorem quotientEquiv_mk (x : ∀ c, G c) :
    quotientEquiv G N (QuotientGroup.mk' (Subgroup.pi Set.univ N) x) =
      fun c ↦ QuotientGroup.mk' (N c) (x c) := by
  rw [quotientEquiv, MulEquiv.trans_apply]
  change QuotientGroup.quotientKerEquivOfSurjective (quotientMap G N) _
    (QuotientGroup.quotientMulEquivOfEq _ (QuotientGroup.mk x)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

variable [Finite C]

omit [∀ c, (N c).Normal] in
theorem commutator_pi : RelationExtension.commutatorKernel (Subgroup.pi Set.univ N) =
    Subgroup.pi Set.univ (fun c ↦ RelationExtension.commutatorKernel (N c)) := by
  unfold RelationExtension.commutatorKernel
  have h := Subgroup.commutator_pi_pi_of_finite N (fun c ↦ (⊤ : Subgroup (G c)))
  simpa only [Subgroup.pi_top] using h

noncomputable def totalEquiv : RelationExtension.Total (Subgroup.pi Set.univ N) ≃*
    ∀ c, RelationExtension.Total (N c) :=
  (QuotientGroup.quotientMulEquivOfEq (commutator_pi G N)).trans
    (quotientEquiv G (fun c ↦ RelationExtension.commutatorKernel (N c)))

@[simp] theorem totalEquiv_mk (x : ∀ c, G c) :
    totalEquiv G N (QuotientGroup.mk' (RelationExtension.commutatorKernel (Subgroup.pi Set.univ N)) x) =
      fun c ↦ QuotientGroup.mk' (RelationExtension.commutatorKernel (N c)) (x c) := by
  rw [totalEquiv, MulEquiv.trans_apply]
  change quotientEquiv G _ (QuotientGroup.quotientMulEquivOfEq _ (QuotientGroup.mk x)) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact quotientEquiv_mk G _ x

theorem totalEquiv_projects (x : RelationExtension.Total (Subgroup.pi Set.univ N)) :
    (fun c ↦ RelationExtension.projection (N c) (totalEquiv G N x c)) =
      quotientEquiv G N (RelationExtension.projection _ x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  simp only [totalEquiv_mk, RelationExtension.projection_mk, quotientEquiv_mk]

noncomputable def kernelEquiv : RelationExtension.Kernel (Subgroup.pi Set.univ N) ≃*
    ∀ c, RelationExtension.Kernel (N c) where
  toFun x c := ⟨totalEquiv G N x c, by
    have h := congrFun (totalEquiv_projects G N x) c
    rw [x.property, map_one] at h
    exact h⟩
  invFun x := ⟨(totalEquiv G N).symm (fun c ↦ (x c).val), by
    apply (quotientEquiv G N).injective
    rw [map_one, ← totalEquiv_projects, MulEquiv.apply_symm_apply]
    exact funext fun c ↦ (x c).property⟩
  left_inv x := by
    apply Subtype.ext
    exact (totalEquiv G N).symm_apply_apply x
  right_inv x := by
    funext c
    apply Subtype.ext
    exact congrFun ((totalEquiv G N).apply_symm_apply (fun c ↦ (x c).val)) c
  map_mul' x y := by
    funext c
    apply Subtype.ext
    exact congrFun ((totalEquiv G N).map_mul x y) c

end SmallPresentationStatements.CentralProduct

namespace SmallPresentationStatements.CentralRelationMap

open scoped commutatorElement

variable {F G : Type} [Group F] [Group G] (N : Subgroup F) (M : Subgroup G)
    [N.Normal] [M.Normal] (e : F ≃* G) (he : N.map e.toMonoidHom = M)

include he in
omit [N.Normal] [M.Normal] in
theorem map_commutatorKernel :
    (RelationExtension.commutatorKernel N).map e.toMonoidHom = RelationExtension.commutatorKernel M := by
  rw [RelationExtension.commutatorKernel, Subgroup.map_commutator, he,
    Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]

noncomputable def congr : RelationExtension.Total N ≃* RelationExtension.Total M :=
  QuotientGroup.congr _ _ e (map_commutatorKernel N M e he)

@[simp] theorem congr_mk (x : F) :
    congr N M e he (QuotientGroup.mk' (RelationExtension.commutatorKernel N) x) =
      QuotientGroup.mk' (RelationExtension.commutatorKernel M) (e x) := rfl

theorem congr_projects (x : RelationExtension.Total N) :
    RelationExtension.projection M (congr N M e he x) =
      QuotientGroup.congr N M e he (RelationExtension.projection N x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

noncomputable def kernelCongr : RelationExtension.Kernel N ≃* RelationExtension.Kernel M where
  toFun x := ⟨congr N M e he x, by
    change RelationExtension.projection M (congr N M e he x) = 1
    rw [congr_projects, x.property, map_one]⟩
  invFun x := ⟨(congr N M e he).symm x, by
    apply (QuotientGroup.congr N M e he).injective
    rw [map_one, ← congr_projects, MulEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((congr N M e he).symm_apply_apply x)
  right_inv x := Subtype.ext ((congr N M e he).apply_symm_apply x)
  map_mul' x y := Subtype.ext ((congr N M e he).map_mul x y)

end SmallPresentationStatements.CentralRelationMap
