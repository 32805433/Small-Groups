module

public import SmallPresentation.SchurKernelQuotient

/-!
# A central extension detecting surjectivity on the Schur multiplier

For any group homomorphism `f : G →* H`, quotient the canonical central
relation extension of `H` by the image of `H₂(f)`. The resulting extension
has zero source obstruction. A section of this particular extension forces
`H₂(f)` to be surjective. All assertions are proved directly in the Hopf model.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology.SchurSurjectivity

variable {G H : Type} [Group G] [Group H] (f : G →* H)

def image : Subgroup (CanonicalTotal H) := SchurKernelQuotient.image (schurMap f).range

theorem image_le_center : image f ≤ Subgroup.center (CanonicalTotal H) :=
  SchurKernelQuotient.image_le_center (schurMap f).range

instance image_normal : (image f).Normal := SchurKernelQuotient.image_normal (schurMap f).range

abbrev Detector := CanonicalTotal H ⧸ image f

def projection : Detector f →* H := SchurKernelQuotient.projection (schurMap f).range

@[simp] theorem projection_mk (x : CanonicalTotal H) :
    projection f (QuotientGroup.mk' (image f) x) = totalEvaluation H x := rfl

theorem projection_surjective : Function.Surjective (projection f) :=
  SchurKernelQuotient.projection_surjective (schurMap f).range

theorem projection_central : UniversalCentralExtension.Central (projection f) :=
  SchurKernelQuotient.projection_central (schurMap f).range

/-- The canonical lifted source map before descending through source relations. -/
def sourceLift : CanonicalTotal G →* Detector f :=
  (QuotientGroup.mk' (image f)).comp (canonicalTotalMap f)

theorem sourceLift_projects : (projection f).comp (sourceLift f) = f.comp (totalEvaluation G) := by
  apply MonoidHom.ext
  intro x
  exact canonicalTotalMap_projection f x

/-- The source Hopf obstruction vanishes by construction of the detector. -/
theorem sourceLift_schur (x : Schur G) : sourceLift f (schurInclusion G x) = 1 := by
  change schurMap f x ∈
    ((SchurKernelQuotient.quotient (schurMap f).range).comp (schurInclusion H)).ker
  rw [SchurKernelQuotient.schur_ker]
  exact ⟨x, rfl⟩

/-- Splitting the detector extension proves surjectivity of the actual Schur map. -/
theorem surjective_of_section (s : H →* Detector f)
    (hs : (projection f).comp s = MonoidHom.id H) : Function.Surjective (schurMap f) := by
  intro x
  have heq : QuotientGroup.mk' (image f) (schurInclusion H x) =
      s (totalEvaluation H (schurInclusion H x)) := by
    apply central_lifts_agree_on_commutator (projection f) (projection_central f)
      (QuotientGroup.mk' (image f)) (s.comp (totalEvaluation H))
    · rw [← MonoidHom.comp_assoc, hs, MonoidHom.id_comp]
      rfl
    · exact x.val.property
  rw [schurInclusion_evaluation, map_one] at heq
  have hx : x ∈
      ((SchurKernelQuotient.quotient (schurMap f).range).comp (schurInclusion H)).ker := heq
  rw [SchurKernelQuotient.schur_ker] at hx
  exact hx

/-- Additive formulation of the detector criterion. -/
theorem map₂_surjective_of_section (s : H →* Detector f)
    (hs : (projection f).comp s = MonoidHom.id H) : Function.Surjective (map₂ f) :=
  surjective_of_section f s hs

end SmallPresentationStatements.Homology.SchurSurjectivity
