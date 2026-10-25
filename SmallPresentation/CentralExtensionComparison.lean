module

public import SmallPresentation.CentralExtensionProjective
public import SmallPresentation.CentralPullbackMaps

/-! Equal Hopf obstructions give equivalent pullback central extensions when
the source has projective abelianization. The proof corrects two free lifts
to agree on all relations and compares their common presentation. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable {E Q A : Type} [Group E] [Group Q] [Group A]

/-- A kernel element together with its centrality witness. -/
def CentralKernel (π : E →* Q) := (π.ker).subgroupOf (Subgroup.center E)

instance (π : E →* Q) : Group (CentralKernel π) := inferInstanceAs
  (Group ((π.ker).subgroupOf (Subgroup.center E)))

instance (π : E →* Q) : CommGroup (CentralKernel π) where
  mul_comm x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp x.1.2 y.1.1).symm

def centralKernelInclusion (π : E →* Q) : CentralKernel π →* E :=
  (Subgroup.center E).subtype.comp ((π.ker).subgroupOf (Subgroup.center E)).subtype

theorem centralKernelInclusion_commute (π : E →* Q) (z : CentralKernel π) (e : E) :
    Commute (centralKernelInclusion π z) e :=
  (Subgroup.mem_center_iff.mp z.1.2 e).symm

@[simp] theorem centralKernelInclusion_projects (π : E →* Q) (z : CentralKernel π) :
    π (centralKernelInclusion π z) = 1 := z.2

def centralRelationRestriction (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f : A →* Q) (σ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A)) :
    RelationExtension.Kernel (canonicalRelations A) →* CentralKernel π := by
  have hp (n : RelationExtension.Kernel (canonicalRelations A)) : π (σ n.1) = 1 := by
    rw [← MonoidHom.comp_apply,hσ]
    change f (totalEvaluation A n.1) = 1
    rw [(totalEvaluation_eq_one_iff A _).mpr n.2,map_one]
  exact
    { toFun := fun n ↦ ⟨⟨σ n.1,hc (hp n)⟩,hp n⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one σ
      map_mul' x y := by apply Subtype.ext; apply Subtype.ext; exact map_mul σ x.1 y.1 }

/-- Correct one free lift by a central character so that two lifts with equal
Hopf obstructions agree on the entire relation kernel. -/
theorem alignCentralLifts [Module.Projective ℤ (H₁ A)]
    (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f g : A →* Q) (σ τ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A))
    (hτ : π.comp τ = g.comp (totalEvaluation A))
    (heq : ∀ x : Schur A, σ x.1.1 = τ x.1.1) :
    ∃ τ' : CanonicalTotal A →* E,
      π.comp τ' = g.comp (totalEvaluation A) ∧
      (∀ n : RelationExtension.Kernel (canonicalRelations A), τ' n.1 = σ n.1) ∧
      (∀ x : CanonicalTotal A, x ∈ commutator (CanonicalTotal A) → τ' x = τ x) := by
  let N := canonicalRelations A
  let χ := centralRelationRestriction π hc g τ hτ / centralRelationRestriction π hc f σ hσ
  have hχ : (RelationExtension.boundary N).ker ≤ χ.ker := by
    intro n hn
    rw [hopf_exact] at hn
    obtain ⟨x,rfl⟩ := hn
    apply Subtype.ext
    apply Subtype.ext
    change τ x.1.1 / σ x.1.1 = 1
    rw [heq]
    simp
  obtain ⟨s,hs⟩ := canonicalAbelianQuotient_split A
  obtain ⟨e,he⟩ := extendCharacter_of_split (RelationExtension.boundary N)
    (canonicalAbelianQuotient A) (canonicalAbelianQuotient_ker A) s hs χ hχ
  let δ : CanonicalTotal A →* CentralKernel π :=
    e.comp (RelationExtension.abelianProjection N)
  let k := (centralKernelInclusion π).comp δ⁻¹
  have hk (x : CanonicalTotal A) (z : E) : Commute (k x) z :=
    centralKernelInclusion_commute π (δ x)⁻¹ z
  let τ' : CanonicalTotal A →* E := MonoidHom.mk' (fun x ↦ τ x * k x) (by
    intro x y
    rw [map_mul,map_mul]
    exact ((hk x (τ y)).mul_mul_mul_comm (τ x) (k y)).symm)
  refine ⟨τ',?_,?_,?_⟩
  · apply MonoidHom.ext
    intro x
    change π (τ x*k x) = g (totalEvaluation A x)
    rw [map_mul,show π (k x) = 1 from centralKernelInclusion_projects π (δ x)⁻¹,mul_one]
    exact DFunLike.congr_fun hτ x
  · intro n
    have hn : centralKernelInclusion π (δ n.1) = τ n.1 / σ n.1 :=
      congrArg (centralKernelInclusion π) (DFunLike.congr_fun he n)
    change τ n.1 * (centralKernelInclusion π (δ n.1))⁻¹ = σ n.1
    rw [hn]
    have hcentral : Commute (τ n.1) (σ n.1) := by
      apply (UniversalCentralExtension.central_iff π).mp hc
      change π (τ n.1) = 1
      rw [← MonoidHom.comp_apply,hτ]
      change g (totalEvaluation A n.1) = 1
      rw [(totalEvaluation_eq_one_iff A _).mpr n.2,map_one]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [← mul_assoc,hcentral.eq]
    simp [mul_assoc]
  · intro x hx
    have hx' : RelationExtension.abelianProjection N x = 1 := by
      change x ∈ (RelationExtension.abelianProjection N).ker
      rw [RelationExtension.abelianProjection_ker]
      exact hx
    change τ x * centralKernelInclusion π ((e (RelationExtension.abelianProjection N x))⁻¹) = τ x
    rw [hx',map_one,inv_one,map_one,mul_one]

def pullbackCover (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f : A →* Q) (σ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A)) :
    CanonicalTotal A × π.ker →* CentralPullback.group π f where
  toFun x := ⟨(σ x.1*x.2.1,totalEvaluation A x.1),by
    change π (σ x.1*x.2.1) = f (totalEvaluation A x.1)
    rw [map_mul,show π x.2.1 = 1 from x.2.2,mul_one]
    exact DFunLike.congr_fun hσ x.1⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    apply Prod.ext
    · change σ (x.1*y.1)*(x.2.1*y.2.1) = (σ x.1*x.2.1)*(σ y.1*y.2.1)
      rw [map_mul]
      exact (show Commute x.2.1 (σ y.1) from
        (UniversalCentralExtension.central_iff π).mp hc _ x.2.2 _).mul_mul_mul_comm _ _ |>.symm
    · exact map_mul _ _ _

theorem pullbackCover_surjective (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f : A →* Q) (σ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A)) :
    Function.Surjective (pullbackCover π hc f σ hσ) := by
  intro y
  let t := totalGenerator A y.1.2
  have ht : totalEvaluation A t = y.1.2 := totalEvaluation_generator A _
  have hz : σ t⁻¹ * y.1.1 ∈ π.ker := by
    change π (σ t⁻¹ * y.1.1) = 1
    rw [map_mul,← MonoidHom.comp_apply,hσ]
    change f (totalEvaluation A t⁻¹)*π y.1.1 = 1
    rw [map_inv,ht,map_inv,y.2,inv_mul_cancel]
  refine ⟨(t,⟨σ t⁻¹*y.1.1,hz⟩),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change σ t * (σ t⁻¹*y.1.1) = y.1.1
    rw [map_inv]
    simp
  · exact ht

theorem pullbackCover_ker_eq (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f g : A →* Q) (σ τ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A))
    (hτ : π.comp τ = g.comp (totalEvaluation A))
    (heq : ∀ n : RelationExtension.Kernel (canonicalRelations A), σ n.1 = τ n.1) :
    (pullbackCover π hc f σ hσ).ker = (pullbackCover π hc g τ hτ).ker := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    have ht : totalEvaluation A x.1 = 1 := congrArg (fun y ↦ y.1.2) hx
    have hn : x.1 ∈ RelationExtension.Kernel (canonicalRelations A) :=
      (totalEvaluation_eq_one_iff A _).mp ht
    apply Subtype.ext
    apply Prod.ext
    · change τ x.1 * x.2.1 = 1
      rw [← heq ⟨x.1,hn⟩]
      exact congrArg (fun y ↦ y.1.1) hx
    · exact ht
  · intro hx
    have ht : totalEvaluation A x.1 = 1 := congrArg (fun y ↦ y.1.2) hx
    have hn : x.1 ∈ RelationExtension.Kernel (canonicalRelations A) :=
      (totalEvaluation_eq_one_iff A _).mp ht
    apply Subtype.ext
    apply Prod.ext
    · change σ x.1 * x.2.1 = 1
      rw [heq ⟨x.1,hn⟩]
      exact congrArg (fun y ↦ y.1.1) hx
    · exact ht

theorem equivOfSurjectiveSameKernel {X Y Z : Type} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (g : X →* Z) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : ∃ e : Y ≃* Z, ∀ x, e (f x) = g x := by
  let a : Y →* Z := f.liftOfSurjective hf ⟨g,hk.le⟩
  let b : Z →* Y := g.liftOfSurjective hg ⟨f,hk.ge⟩
  have ha (x : X) : a (f x) = g x := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hb (x : X) : b (g x) = f x := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨{ a with invFun := b, left_inv := ?_,right_inv := ?_ },ha⟩
  · intro y
    obtain ⟨x,rfl⟩ := hf y
    change b (a (f x)) = f x
    rw [ha,hb]
  · intro z
    obtain ⟨x,rfl⟩ := hg z
    change a (b (g x)) = g x
    rw [hb,ha]

theorem pullbackOverEquiv_of_relation_agreement
    (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f g : A →* Q) (σ τ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A))
    (hτ : π.comp τ = g.comp (totalEvaluation A))
    (heq : ∀ n : RelationExtension.Kernel (canonicalRelations A), σ n.1 = τ n.1) :
    Nonempty (CentralPullback.OverEquiv π f g) := by
  obtain ⟨e,he⟩ := equivOfSurjectiveSameKernel (pullbackCover π hc f σ hσ)
    (pullbackCover π hc g τ hτ) (pullbackCover_surjective π hc f σ hσ)
    (pullbackCover_surjective π hc g τ hτ) (pullbackCover_ker_eq π hc f g σ τ hσ hτ heq)
  refine ⟨{ equiv := e,over := ?_,kernel := ?_ }⟩
  · apply MonoidHom.ext
    intro x
    obtain ⟨y,rfl⟩ := pullbackCover_surjective π hc f σ hσ x
    change CentralPullback.second π g (e (pullbackCover π hc f σ hσ y)) = _
    rw [he]
    rfl
  · intro z
    have hleft : pullbackCover π hc f σ hσ (1,z) = CentralPullback.kernelInclusion π f z := by
      apply Subtype.ext
      simp [pullbackCover,CentralPullback.kernelInclusion]
    rw [← hleft,he]
    apply Subtype.ext
    simp [pullbackCover,CentralPullback.kernelInclusion]

/-- Pullbacks with equal induced Hopf obstructions are equivalent over the
source and induce the identity on the common central kernel. -/
theorem pullbackOverEquiv_of_hopf_eq [Module.Projective ℤ (H₁ A)]
    (π : E →* Q) (hc : UniversalCentralExtension.Central π)
    (f g : A →* Q) (σ τ : CanonicalTotal A →* E)
    (hσ : π.comp σ = f.comp (totalEvaluation A))
    (hτ : π.comp τ = g.comp (totalEvaluation A))
    (heq : ∀ x : Schur A, σ x.1.1 = τ x.1.1) :
    Nonempty (CentralPullback.OverEquiv π f g) := by
  obtain ⟨τ',hτ',hr,_⟩ := alignCentralLifts π hc f g σ τ hσ hτ heq
  exact pullbackOverEquiv_of_relation_agreement π hc f g σ τ' hσ hτ' (fun n ↦ (hr n).symm)

end SmallPresentationStatements.Homology
