module

public import SmallPresentation.KunnethTotal

/-! Central extensions retaining a prescribed quotient of the Schur multiplier. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G : Type) [Group G]

/-- Inclusion of the canonical Hopf kernel in the central relation extension. -/
def schurInclusion : Schur G →* CanonicalTotal G :=
  (commutator (CanonicalTotal G)).subtype.comp (Schur G).subtype

@[simp] theorem schurInclusion_evaluation (x : Schur G) :
    totalEvaluation G (schurInclusion G x) = 1 :=
  (totalEvaluation_eq_one_iff G _).mpr x.property

variable {G} {H E : Type} [Group H] [Group E]

/-- Any lift to a central extension detects every element killed by the Schur map.
This is useful for proving injectivity or an exact kernel formula by constructing
a central extension in which the required source classes survive. -/
theorem schurMap_ker_le_centralLift_ker (f : G →* H) (π : E →* H)
    (hπ : Function.Surjective π) (hc : UniversalCentralExtension.Central π)
    (σ : CanonicalTotal G →* E) (hσ : π.comp σ = f.comp (totalEvaluation G)) :
    (schurMap f).ker ≤ (σ.comp (schurInclusion G)).ker := by
  classical
  let s : H → E := fun h ↦ Classical.choose (hπ h)
  have hs : ∀ h, π (s h) = h := fun h ↦ Classical.choose_spec (hπ h)
  let L := canonicalTotalLift π hc s hs
  have hL : π.comp L = totalEvaluation H := canonicalTotalLift_projection π hc s hs
  intro x hx
  have heq : L (canonicalTotalMap f (schurInclusion G x)) = σ (schurInclusion G x) := by
    apply central_lifts_agree_on_commutator π hc
      (L.comp (canonicalTotalMap f)) σ
    · rw [← MonoidHom.comp_assoc, hL, hσ]
      apply MonoidHom.ext
      intro y
      exact canonicalTotalMap_projection f y
    · exact x.val.property
  have hx' : canonicalTotalMap f (schurInclusion G x) = 1 :=
    congrArg (fun z : Schur H ↦ z.val.val) hx
  change σ (schurInclusion G x) = 1
  rw [← heq, hx', map_one]

theorem schurMap_injective_of_centralLift (f : G →* H) (π : E →* H)
    (hπ : Function.Surjective π) (hc : UniversalCentralExtension.Central π)
    (σ : CanonicalTotal G →* E) (hσ : π.comp σ = f.comp (totalEvaluation G))
    (hi : Function.Injective (σ.comp (schurInclusion G))) :
    Function.Injective (schurMap f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  exact (schurMap_ker_le_centralLift_ker f π hπ hc σ hσ).trans
    ((MonoidHom.ker_eq_bot_iff _).mpr hi).le

end SmallPresentationStatements.Homology

namespace SmallPresentationStatements.Homology.SchurKernelQuotient

variable {G : Type} [Group G] (S : Subgroup (Schur G))

def image : Subgroup (CanonicalTotal G) := S.map (schurInclusion G)

theorem image_le_center : image S ≤ Subgroup.center (CanonicalTotal G) := by
  rintro _ ⟨x, _, rfl⟩
  apply totalEvaluation_central G
  exact schurInclusion_evaluation G x

instance image_normal : (image S).Normal := Subgroup.normal_of_le_center (image_le_center S)

abbrev Total := CanonicalTotal G ⧸ image S

def quotient : CanonicalTotal G →* Total S := QuotientGroup.mk' (image S)

def projection : Total S →* G := QuotientGroup.lift _ (totalEvaluation G) (by
  rintro _ ⟨x, _, rfl⟩
  exact schurInclusion_evaluation G x)

@[simp] theorem projection_quotient (x : CanonicalTotal G) :
    projection S (quotient S x) = totalEvaluation G x := rfl

theorem projection_surjective : Function.Surjective (projection S) := by
  intro g
  exact ⟨quotient S (totalGenerator G g), totalEvaluation_generator G g⟩

theorem projection_central : UniversalCentralExtension.Central (projection S) := by
  apply (UniversalCentralExtension.central_iff _).mpr
  intro z hz x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (image S) z
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (image S) x
  change totalEvaluation G a = 1 at hz
  have hab := (UniversalCentralExtension.central_iff _).mp (totalEvaluation_central G) a hz b
  exact (map_mul (QuotientGroup.mk' (image S)) a b).symm.trans
    ((congrArg (QuotientGroup.mk' (image S)) hab).trans (map_mul _ b a))

/-- Precisely the prescribed subgroup of the Schur multiplier is killed. -/
theorem schur_ker : ((quotient S).comp (schurInclusion G)).ker = S := by
  ext x
  change QuotientGroup.mk' (image S) (schurInclusion G x) = 1 ↔ x ∈ S
  have h : QuotientGroup.mk' (image S) (schurInclusion G x) = 1 ↔
      schurInclusion G x ∈ image S := QuotientGroup.eq_one_iff _
  rw [h]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hxy : y = x := by
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    rw [← hxy]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable {A : Type} [Group A] (l r : A →* G)

/-- Equality of Schur maps modulo the prescribed subgroup is exactly the equality
of their central obstructions in this extension. -/
theorem equal_obstruction
    (h : ∀ x : Schur A, schurMap l x * (schurMap r x)⁻¹ ∈ S)
    (x : Schur A) :
    quotient S (canonicalTotalMap l (schurInclusion A x)) =
      quotient S (canonicalTotalMap r (schurInclusion A x)) := by
  apply mul_inv_eq_one.mp
  have hh : schurMap l x * (schurMap r x)⁻¹ ∈
      ((quotient S).comp (schurInclusion G)).ker := by
    rw [schur_ker]
    exact h x
  change quotient S (schurInclusion G (schurMap l x * (schurMap r x)⁻¹)) = 1 at hh
  have hl : schurInclusion G (schurMap l x) = canonicalTotalMap l (schurInclusion A x) := rfl
  have hr : schurInclusion G (schurMap r x) = canonicalTotalMap r (schurInclusion A x) := rfl
  simpa only [map_mul, map_inv, hl, hr] using hh

end SmallPresentationStatements.Homology.SchurKernelQuotient
