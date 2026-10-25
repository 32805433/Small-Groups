module

public import SmallPresentation.HNNFamily

/-!
# Central lifting across arbitrary HNN families

Conjugation defects of a lifted vertex map are homomorphisms from the edge
abelianizations to the central kernel. A split injective degree-one boundary
allows all these defects to be corrected at once. This is the central-extension
obstruction calculation behind the low-degree Mayer--Vietoris sequence, proved
directly from the HNN universal property.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology.HNNFamilyPresentation

open DirectSum UniversalCentralExtension

variable {I G K E Q : Type} {A : I → Type}
  [Group G] [Group K] [Group E] [Group Q] [∀ i, Group (A i)]
variable {l r : ∀ i, A i →* G} (P : HNNFamilyPresentation l r K)
variable (π : E →* Q) (hc : Central π)

@[reducible] def centralKernelCommGroup : CommGroup π.ker where
  mul_comm x y := Subtype.ext ((central_iff π).mp hc x x.property y)

variable (f : K →* Q) (σ : G →* E) (hσ : π.comp σ = f.comp P.base)
variable (t : I → E) (ht : ∀ i, π (t i) = f (P.stable i))

include hσ ht in
theorem defect_projects (i : I) :
    π.comp ((MulAut.conj (t i)⁻¹).toMonoidHom.comp (σ.comp (l i))) =
      π.comp (σ.comp (r i)) := by
  apply MonoidHom.ext
  intro a
  change π ((t i)⁻¹ * σ (l i a) * ((t i)⁻¹)⁻¹) = π (σ (r i a))
  simp only [inv_inv, map_mul, map_inv, ht]
  rw [show π (σ (l i a)) = f (P.base (l i a)) from DFunLike.congr_fun hσ _,
    show π (σ (r i a)) = f (P.base (r i a)) from DFunLike.congr_fun hσ _]
  simpa only [map_mul, map_inv] using congrArg f (P.conjugates i a)

/-- The conjugation defect lies in the central kernel and is multiplicative. -/
def defect (i : I) : A i →* π.ker :=
  (differenceHom π hc ((MulAut.conj (t i)⁻¹).toMonoidHom.comp (σ.comp (l i)))
    (σ.comp (r i)) (P.defect_projects π f σ hσ t ht i)).codRestrict _ (by
      intro a
      change π (((t i)⁻¹ * σ (l i a) * ((t i)⁻¹)⁻¹) * (σ (r i a))⁻¹) = 1
      rw [map_mul, map_inv]
      have h := DFunLike.congr_fun (P.defect_projects π f σ hσ t ht i) a
      change π ((t i)⁻¹ * σ (l i a) * ((t i)⁻¹)⁻¹) = π (σ (r i a)) at h
      rw [h, mul_inv_cancel])

@[simp] theorem defect_val (i : I) (a : A i) :
    (P.defect π hc f σ hσ t ht i a : E) =
      (t i)⁻¹ * σ (l i a) * t i * (σ (r i a))⁻¹ := by
  simp only [defect, MonoidHom.codRestrict_apply, differenceHom, MonoidHom.coe_mk,
    OneHom.coe_mk, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]

/-- Defects factor canonically through the edge abelianizations. -/
def defect₁ (i : I) : H₁ (A i) →+ Additive π.ker := by
  let := centralKernelCommGroup π hc
  exact (Abelianization.lift (P.defect π hc f σ hσ t ht i)).toAdditive

@[simp] theorem defect₁_of (i : I) (a : A i) :
    P.defect₁ π hc f σ hσ t ht i (Additive.ofMul (Abelianization.of a)) =
      Additive.ofMul (P.defect π hc f σ hσ t ht i a) := by
  rfl

variable [DecidableEq I]

/-- Collect the edge obstructions into one map from the direct sum. -/
noncomputable def totalDefect : (⨁ i, H₁ (A i)) →+ Additive π.ker := by
  let := centralKernelCommGroup π hc
  exact DirectSum.toAddMonoid fun i ↦ P.defect₁ π hc f σ hσ t ht i

@[simp] theorem totalDefect_of (i : I) (x : H₁ (A i)) :
    P.totalDefect π hc f σ hσ t ht (DirectSum.of _ i x) =
      P.defect₁ π hc f σ hσ t ht i x := by
  let := centralKernelCommGroup π hc
  exact DirectSum.toAddMonoid_of (fun i ↦ P.defect₁ π hc f σ hσ t ht i) i x

omit [DecidableEq I] in
/-- Changing a base lift by a homomorphism to the central kernel. -/
def adjust (τ : G →* π.ker) : G →* E where
  toFun g := σ g * (τ g : E)⁻¹
  map_one' := by simp
  map_mul' x y := by
    have hxy : (τ x : E)⁻¹ * σ y = σ y * (τ x : E)⁻¹ :=
      (central_iff π).mp hc _ (π.ker.inv_mem (τ x).property) _
    have hτ : (τ y : E)⁻¹ * (τ x : E)⁻¹ = (τ x : E)⁻¹ * (τ y : E)⁻¹ :=
      (central_iff π).mp hc _ (π.ker.inv_mem (τ y).property) _
    simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
    rw [hτ]
    calc
      σ x * σ y * ((τ x : E)⁻¹ * (τ y : E)⁻¹) =
        σ x * (σ y * (τ x : E)⁻¹) * (τ y : E)⁻¹ := by group
      _ = σ x * ((τ x : E)⁻¹ * σ y) * (τ y : E)⁻¹ := by rw [hxy]
      _ = _ := by group

omit [DecidableEq I] in
include hσ in
theorem adjust_projects (τ : G →* π.ker) :
    π.comp (adjust π hc σ τ) = f.comp P.base := by
  apply MonoidHom.ext
  intro g
  change π (σ g * (τ g : E)⁻¹) = f (P.base g)
  rw [map_mul, map_inv, show π (τ g) = 1 from (τ g).property, inv_one, mul_one]
  exact DFunLike.congr_fun hσ g

omit [DecidableEq I] in
/-- A correction whose edge differences are the defects makes the conjugation equations exact. -/
theorem adjust_conjugates (τ : G →* π.ker)
    (hτ : ∀ i a, (τ (l i a) : E) * (τ (r i a) : E)⁻¹ =
      (P.defect π hc f σ hσ t ht i a : E)) (i : I) (a : A i) :
    (t i)⁻¹ * adjust π hc σ τ (l i a) * t i = adjust π hc σ τ (r i a) := by
  have hL : (τ (l i a) : E)⁻¹ * t i = t i * (τ (l i a) : E)⁻¹ :=
    (central_iff π).mp hc _ (π.ker.inv_mem (τ (l i a)).property) _
  have hR : (τ (r i a) : E)⁻¹ * σ (r i a) = σ (r i a) * (τ (r i a) : E)⁻¹ :=
    (central_iff π).mp hc _ (π.ker.inv_mem (τ (r i a)).property) _
  have hLc : (τ (l i a) : E) * (σ (r i a) * (τ (r i a) : E)⁻¹) =
      (σ (r i a) * (τ (r i a) : E)⁻¹) * (τ (l i a) : E) :=
    (central_iff π).mp hc _ (τ (l i a)).property _
  have hd := hτ i a
  rw [P.defect_val] at hd
  have heq : (t i)⁻¹ * σ (l i a) * t i =
      (τ (l i a) : E) * (τ (r i a) : E)⁻¹ * σ (r i a) := by
    have hh := congrArg (fun z : E ↦ z * σ (r i a)) hd.symm
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  change (t i)⁻¹ * (σ (l i a) * (τ (l i a) : E)⁻¹) * t i =
    σ (r i a) * (τ (r i a) : E)⁻¹
  calc
    _ = ((t i)⁻¹ * σ (l i a) * t i) * (τ (l i a) : E)⁻¹ := by
      simp only [mul_assoc]
      rw [hL]
    _ = ((τ (l i a) : E) * (τ (r i a) : E)⁻¹ * σ (r i a)) *
        (τ (l i a) : E)⁻¹ := by rw [heq]
    _ = (τ (l i a) : E) * (σ (r i a) * (τ (r i a) : E)⁻¹) *
        (τ (l i a) : E)⁻¹ := by rw [mul_assoc _ _ (σ _), hR]
    _ = _ := by rw [hLc]; group

/-- A left inverse to the degree-one boundary gives an explicit central correction. -/
noncomputable def boundaryCorrection (s : H₁ G →+ (⨁ i, H₁ (A i))) : G →* π.ker where
  toFun g := (P.totalDefect π hc f σ hσ t ht
    (s (Additive.ofMul (Abelianization.of g)))).toMul
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul]
    change (P.totalDefect π hc f σ hσ t ht
      (s (Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of y)))).toMul = _
    rw [map_add, map_add]
    rfl

theorem boundaryCorrection_defect (s : H₁ G →+ (⨁ i, H₁ (A i)))
    (hs : s.comp (boundary₁ (l := l) (r := r)) = AddMonoidHom.id _) (i : I) (a : A i) :
    (P.boundaryCorrection π hc f σ hσ t ht s (l i a) : E) *
        (P.boundaryCorrection π hc f σ hσ t ht s (r i a) : E)⁻¹ =
      (P.defect π hc f σ hσ t ht i a : E) := by
  let x := Additive.ofMul (Abelianization.of a)
  have hx := DFunLike.congr_fun hs (DirectSum.of (fun i ↦ H₁ (A i)) i x)
  change s (boundary₁ (l := l) (r := r) (DirectSum.of _ i x)) = DirectSum.of _ i x at hx
  rw [boundary₁_of] at hx
  have hd := congrArg (P.totalDefect π hc f σ hσ t ht) hx
  rw [map_sub, map_sub, P.totalDefect_of, P.defect₁_of] at hd
  have hm := congrArg Additive.toMul hd
  change P.boundaryCorrection π hc f σ hσ t ht s (l i a) /
      P.boundaryCorrection π hc f σ hσ t ht s (r i a) =
    P.defect π hc f σ hσ t ht i a at hm
  simpa only [Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using
    congrArg Subtype.val hm

/-- Correcting the base lift does not change its restriction to the derived subgroup. -/
theorem boundaryCorrection_commutator (s : H₁ G →+ (⨁ i, H₁ (A i)))
    (g : G) (hg : g ∈ commutator G) : P.boundaryCorrection π hc f σ hσ t ht s g = 1 := by
  have hga : Abelianization.of g = 1 := by
    change g ∈ (Abelianization.of : G →* Abelianization G).ker
    rw [Abelianization.ker_of]
    exact hg
  change (P.totalDefect π hc f σ hσ t ht (s (Additive.ofMul (Abelianization.of g)))).toMul = 1
  rw [hga]
  change (P.totalDefect π hc f σ hσ t ht (s 0)).toMul = 1
  rw [map_zero, map_zero]
  rfl

include hc hσ ht in
/-- With split injective degree-one boundary, a lifted vertex map extends to a
lift of the whole HNN presentation after a central correction. The correction
vanishes on the derived subgroup. No edge injectivity or degree-two exactness
theorem is required. -/
theorem lift_of_split_boundary (s : H₁ G →+ (⨁ i, H₁ (A i)))
    (hs : s.comp (boundary₁ (l := l) (r := r)) = AddMonoidHom.id _) :
    ∃ L : K →* E, π.comp L = f ∧
      (∀ g ∈ commutator G, L (P.base g) = σ g) ∧ (∀ i, L (P.stable i) = t i) := by
  let τ := P.boundaryCorrection π hc f σ hσ t ht s
  have hτ : ∀ i a, (τ (l i a) : E) * (τ (r i a) : E)⁻¹ =
      (P.defect π hc f σ hσ t ht i a : E) :=
    P.boundaryCorrection_defect π hc f σ hσ t ht s hs
  let σ' := adjust π hc σ τ
  let L := P.lift σ' t (P.adjust_conjugates π hc f σ hσ t ht τ hτ)
  refine ⟨L, ?_, ?_, ?_⟩
  · apply P.hom_ext
    · intro g
      change π (L (P.base g)) = f (P.base g)
      rw [show L (P.base g) = σ' g from P.lift_base _ _ _ g]
      exact DFunLike.congr_fun (P.adjust_projects π hc f σ hσ τ) g
    · intro i
      change π (L (P.stable i)) = f (P.stable i)
      rw [show L (P.stable i) = t i from P.lift_stable _ _ _ i, ht]
  · intro g hg
    rw [show L (P.base g) = σ' g from P.lift_base _ _ _ g]
    change σ g * (τ g : E)⁻¹ = σ g
    rw [show τ g = 1 from P.boundaryCorrection_commutator π hc f σ hσ t ht s g hg]
    simp
  · intro i
    exact P.lift_stable _ _ _ i

include hc hσ in
/-- The stable-letter lifts may be chosen whenever the central extension is onto. -/
theorem lift_of_split_boundary_of_surjective (hπ : Function.Surjective π)
    (s : H₁ G →+ (⨁ i, H₁ (A i)))
    (hs : s.comp (boundary₁ (l := l) (r := r)) = AddMonoidHom.id _) :
    ∃ L : K →* E, π.comp L = f ∧ ∀ g ∈ commutator G, L (P.base g) = σ g := by
  classical
  let t : I → E := fun i ↦ Classical.choose (hπ (f (P.stable i)))
  have ht : ∀ i, π (t i) = f (P.stable i) := fun i ↦ Classical.choose_spec (hπ _)
  obtain ⟨L, hL, hbase, _⟩ := P.lift_of_split_boundary π hc f σ hσ t ht s hs
  exact ⟨L, hL, hbase⟩

end SmallPresentationStatements.Homology.HNNFamilyPresentation
