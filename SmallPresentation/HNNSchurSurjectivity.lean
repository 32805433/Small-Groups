module

public import SmallPresentation.HNNCentralLifting
public import SmallPresentation.CentralExtensionProjective
public import SmallPresentation.SchurSurjectivity

/-!
# A proved degree-two surjectivity theorem for HNN families

If the vertex abelianization is projective and the degree-one edge boundary
has a left inverse, the vertex map is onto on integral degree-two homology.
The proof constructs a section of the central extension detecting the cokernel;
it does not require a general Mayer--Vietoris sequence or
injectivity of the attaching homomorphisms.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology.HNNFamilyPresentation

open DirectSum

variable {I G K : Type} {A : I → Type}
  [Group G] [Group K] [∀ i, Group (A i)] [DecidableEq I]
variable {l r : ∀ i, A i →* G} (P : HNNFamilyPresentation l r K)

/-- Split degree-one boundary and projective vertex abelianization imply
surjectivity of the actual vertex map on the Schur multiplier. -/
theorem map₂_base_surjective_of_split_boundary [Module.Projective ℤ (H₁ G)]
    (s : H₁ G →+ (⨁ i, H₁ (A i)))
    (hs : s.comp (boundary₁ (l := l) (r := r)) = AddMonoidHom.id _) :
    Function.Surjective (map₂ P.base) := by
  let π := SchurSurjectivity.projection P.base
  have hc := SchurSurjectivity.projection_central P.base
  obtain ⟨σ, hσ, _⟩ := centralLift_of_hopf_zero π hc P.base
    (SchurSurjectivity.sourceLift P.base) (SchurSurjectivity.sourceLift_projects P.base)
    (SchurSurjectivity.sourceLift_schur P.base)
  have hσ' : π.comp σ = (MonoidHom.id K).comp P.base := by
    simpa only [MonoidHom.id_comp] using hσ
  obtain ⟨L, hL, _⟩ := P.lift_of_split_boundary_of_surjective π hc (MonoidHom.id K) σ hσ'
    (SchurSurjectivity.projection_surjective P.base) s hs
  exact SchurSurjectivity.map₂_surjective_of_section P.base L hL

end SmallPresentationStatements.Homology.HNNFamilyPresentation
