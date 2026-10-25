module

public import SmallPresentation.UniversalCentralExtension
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! A canonical Hopf model for the integral Schur multiplier. All groups here
are fixed concrete quotients. Independence of the free presentation is proved
using free lifts and central relation extensions. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable {X Y : Type} (N : Subgroup (FreeGroup X)) (M : Subgroup (FreeGroup Y))
    [N.Normal] [M.Normal]

abbrev PresentationKernel := (UniversalCentralExtension.derivedProjection N).ker

instance presentationKernelCommGroup : CommGroup (PresentationKernel N) where
  mul_comm x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact RelationExtension.kernel_central N x.1.1 x.property y.1.1

def totalMap (f : FreeGroup X →* FreeGroup Y) (hf : N ≤ M.comap f) :
    RelationExtension.Total N →* RelationExtension.Total M :=
  QuotientGroup.map _ _ f (by
    apply Subgroup.commutator_le.mpr
    intro n hn x _
    change f ⁅n,x⁆ ∈ ⁅M,(⊤ : Subgroup (FreeGroup Y))⁆
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hf hn) (Subgroup.mem_top _))

theorem totalMap_projection (f : FreeGroup X →* FreeGroup Y) (hf : N ≤ M.comap f)
    (x : RelationExtension.Total N) :
    RelationExtension.projection M (totalMap N M f hf x) =
      QuotientGroup.map N M f hf (RelationExtension.projection N x) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ x
  rfl

def derivedMap (f : FreeGroup X →* FreeGroup Y) (hf : N ≤ M.comap f) :
    UniversalCentralExtension.Derived N →* UniversalCentralExtension.Derived M :=
  ((totalMap N M f hf).comp (commutator (RelationExtension.Total N)).subtype).codRestrict _ (by
    intro x
    apply (show (commutator (RelationExtension.Total N)).map (totalMap N M f hf) ≤
      commutator (RelationExtension.Total M) from by
        rw [map_commutator_eq]
        exact Subgroup.commutator_mono le_top le_top)
    exact ⟨x,x.property,rfl⟩)

def presentationMap (f : FreeGroup X →* FreeGroup Y) (hf : N ≤ M.comap f) :
    PresentationKernel N →* PresentationKernel M :=
  ((derivedMap N M f hf).comp (PresentationKernel N).subtype).codRestrict _ (by
    intro x
    change RelationExtension.projection M (totalMap N M f hf x.1.1) = 1
    rw [totalMap_projection, show RelationExtension.projection N x.1.1 = 1 from x.property,
      map_one])

variable (G : Type) [Group G]

def freeProjection : FreeGroup G →* G := FreeGroup.lift id

abbrev canonicalRelations := (freeProjection G).ker

abbrev Schur := PresentationKernel (canonicalRelations G)
abbrev H₂ := Additive (Schur G)
abbrev H₁ := Additive (Abelianization G)

variable {G} {H : Type} [Group H]

theorem freeProjection_map (f : G →* H) :
    (freeProjection H).comp (FreeGroup.map f) = f.comp (freeProjection G) := by
  apply FreeGroup.ext_hom
  intro g
  simp [freeProjection]

theorem canonicalRelations_map (f : G →* H) :
    canonicalRelations G ≤ (canonicalRelations H).comap (FreeGroup.map f) := by
  intro x hx
  change freeProjection H (FreeGroup.map f x) = 1
  have hh := DFunLike.congr_fun (freeProjection_map f) x
  change freeProjection H (FreeGroup.map f x) = f (freeProjection G x) at hh
  rw [hh, show freeProjection G x = 1 from hx, map_one]

def schurMap (f : G →* H) : Schur G →* Schur H :=
  presentationMap (canonicalRelations G) (canonicalRelations H)
    (FreeGroup.map f) (canonicalRelations_map f)

@[simp] theorem schurMap_id (x : Schur G) : schurMap (MonoidHom.id G) x = x := by
  apply Subtype.ext
  apply Subtype.ext
  change totalMap _ _ _ (canonicalRelations_map (MonoidHom.id G)) x.1.1 = x.1.1
  obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective _ x.1.1
  rw [← hz]
  simp only [totalMap, QuotientGroup.map_mk']
  exact congrArg (QuotientGroup.mk' _) (FreeGroup.map.id z)

@[simp] theorem schurMap_comp {K : Type} [Group K] (f : G →* H) (g : H →* K) (x : Schur G) :
    schurMap g (schurMap f x) = schurMap (g.comp f) x := by
  apply Subtype.ext
  apply Subtype.ext
  change totalMap _ _ _ (canonicalRelations_map g)
    (totalMap _ _ _ (canonicalRelations_map f) x.1.1) =
      totalMap _ _ _ (canonicalRelations_map (g.comp f)) x.1.1
  obtain ⟨z,hz⟩ := QuotientGroup.mk'_surjective _ x.1.1
  rw [← hz]
  simp only [totalMap, QuotientGroup.map_mk', QuotientGroup.map_mk]
  exact congrArg (QuotientGroup.mk' _) (FreeGroup.map.comp f g z)

noncomputable def schurEquiv (e : G ≃* H) : Schur G ≃* Schur H where
  toFun := schurMap e.toMonoidHom
  invFun := schurMap e.symm.toMonoidHom
  left_inv x := by
    rw [schurMap_comp, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G from by ext; simp]
    exact schurMap_id x
  right_inv x := by
    rw [schurMap_comp, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H from by ext; simp]
    exact schurMap_id x
  map_mul' := map_mul _

def map₂ (f : G →* H) : H₂ G →+ H₂ H := (schurMap f).toAdditive

def map₁ (f : G →* H) : H₁ G →+ H₁ H := (Abelianization.map f).toAdditive


@[simp] theorem map₁_comp {K : Type} [Group K] (f : G →* H) (g : H →* K) (x : H₁ G) :
    map₁ g (map₁ f x) = map₁ (g.comp f) x := by
  exact DFunLike.congr_fun (Abelianization.map_comp f g) x

@[simp] theorem map₁_id (x : H₁ G) : map₁ (MonoidHom.id G) x = x := by
  exact DFunLike.congr_fun Abelianization.map_id x

@[simp] theorem map₁_one (x : H₁ G) : map₁ (1 : G →* H) x = 0 := by
  have h : Abelianization.map (1 : G →* H) = 1 := by
    apply Abelianization.hom_ext
    ext g
    simp
  exact DFunLike.congr_fun h x

/-- Lifts to a central extension agree on the derived subgroup. -/
theorem central_lifts_agree_on_commutator {U E Q : Type} [Group U] [Group E] [Group Q]
    (π : E →* Q) (hc : UniversalCentralExtension.Central π) (f g : U →* E)
    (heq : π.comp f = π.comp g) (x : U) (hx : x ∈ commutator U) : f x = g x := by
  let δ := UniversalCentralExtension.differenceHom π hc f g heq
  have hδ (y : U) : δ y ∈ π.ker := by
    change π (f y * (g y)⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [show π (f y) = π (g y) from DFunLike.congr_fun heq y]
    exact mul_inv_cancel _
  have hkill : commutator U ≤ δ.ker := by
    apply Subgroup.commutator_le.mpr
    intro y _ z _
    change δ ⁅y,z⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (UniversalCentralExtension.central_iff π).mp hc _ (hδ y) _
  exact mul_inv_eq_one.mp (hkill hx)

noncomputable def quotientLift (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M) :
    FreeGroup X →* FreeGroup Y :=
  FreeGroup.lift fun x ↦ Classical.choose
    (QuotientGroup.mk'_surjective M (e (QuotientGroup.mk' N (FreeGroup.of x))))

theorem quotientLift_spec (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M) :
    (QuotientGroup.mk' M).comp (quotientLift N M e) = e.comp (QuotientGroup.mk' N) := by
  apply FreeGroup.ext_hom
  intro x
  change QuotientGroup.mk' M (FreeGroup.lift _ (FreeGroup.of x)) = _
  rw [FreeGroup.lift_apply_of]
  exact Classical.choose_spec (QuotientGroup.mk'_surjective M
    (e (QuotientGroup.mk' N (FreeGroup.of x))))

theorem quotientLift_relations (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M) :
    N ≤ M.comap (quotientLift N M e) := by
  intro x hx
  change quotientLift N M e x ∈ M
  apply (QuotientGroup.eq_one_iff _).mp
  have h := DFunLike.congr_fun (quotientLift_spec N M e) x
  change QuotientGroup.mk' M (quotientLift N M e x) = e (QuotientGroup.mk' N x) at h
  change QuotientGroup.mk' M (quotientLift N M e x) = 1
  rw [h]
  have hx' : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [hx', map_one]

noncomputable def liftedTotal (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M) :
    RelationExtension.Total N →* RelationExtension.Total M :=
  totalMap N M (quotientLift N M e) (quotientLift_relations N M e)

theorem liftedTotal_projection (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M)
    (x : RelationExtension.Total N) :
    RelationExtension.projection M (liftedTotal N M e x) = e (RelationExtension.projection N x) := by
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact DFunLike.congr_fun (quotientLift_spec N M e) x

noncomputable def liftedKernel (e : FreeGroup X ⧸ N →* FreeGroup Y ⧸ M) :
    PresentationKernel N →* PresentationKernel M :=
  presentationMap N M (quotientLift N M e) (quotientLift_relations N M e)

theorem liftedKernel_inverse (e : FreeGroup X ⧸ N ≃* FreeGroup Y ⧸ M)
    (x : PresentationKernel N) :
    liftedKernel M N e.symm.toMonoidHom (liftedKernel N M e.toMonoidHom x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  change liftedTotal M N e.symm.toMonoidHom (liftedTotal N M e.toMonoidHom x.1.1) = x.1.1
  apply central_lifts_agree_on_commutator (RelationExtension.projection N)
    ((UniversalCentralExtension.central_iff _).mpr (RelationExtension.kernel_central N))
    ((liftedTotal M N e.symm.toMonoidHom).comp (liftedTotal N M e.toMonoidHom))
    (MonoidHom.id _)
  · ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, liftedTotal_projection]
    exact e.symm_apply_apply _
  · exact x.1.property

/-- Hopf kernels are independent of the free presentation, by free lifts and
centrality of the relation extension. -/
noncomputable def presentationKernelEquiv
    (e : FreeGroup X ⧸ N ≃* FreeGroup Y ⧸ M) : PresentationKernel N ≃* PresentationKernel M where
  toFun := liftedKernel N M e.toMonoidHom
  invFun := liftedKernel M N e.symm.toMonoidHom
  left_inv := liftedKernel_inverse N M e
  right_inv := liftedKernel_inverse M N e.symm
  map_mul' := map_mul _

theorem presentation_kernel_equiv (N : Subgroup (FreeGroup X)) [N.Normal] :
    Nonempty (PresentationKernel N ≃* Schur (FreeGroup X ⧸ N)) := by
  let G := FreeGroup X ⧸ N
  have hs : Function.Surjective (freeProjection G) := by
    intro g
    exact ⟨FreeGroup.of g, FreeGroup.lift_apply_of⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective (freeProjection G) hs
  exact ⟨presentationKernelEquiv N (canonicalRelations G) e.symm⟩

end SmallPresentationStatements.Homology
