module

public import SmallPresentation.HNNCentralExtension
public import SmallPresentation.HNNFamilyTwo
public import SmallPresentation.CentralPullbackMaps

/-! Extension of a central extension through two actual HNN identifications.
The new vertex embedding is injective by the ordinary HNN normal-form theorem. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open UniversalGroup UniversalCentralExtension

variable {G E A B : Type} [Group G] [Group E] [Group A] [Group B]
variable (l₁ r₁ : A →* G) (l₂ r₂ : B →* G)
variable (hl₁ : Function.Injective l₁) (hr₁ : Function.Injective r₁)
    (hl₂ : Function.Injective l₂) (hr₂ : Function.Injective r₂)

/-- Compatible identifications of the two pullback central extensions give a
central extension of the actual iterated HNN group, retaining the entire vertex
extension injectively. -/
theorem twoHNN_central_extension (π : E →* G) (hπ : Function.Surjective π) (hc : Central π)
    (e₁ : CentralPullback.OverEquiv π l₁ r₁) (e₂ : CentralPullback.OverEquiv π l₂ r₂) :
    ∃ (L : Type) (_ : Group L)
      (q : L →* TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂) (j : E →* L),
      Function.Surjective q ∧ Central q ∧ Function.Injective j ∧
      q.comp j = (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂).comp π := by
  let A' := CentralPullback.group π l₁
  let B' := CentralPullback.group π l₂
  let u₁ : A' →* E := CentralPullback.first π l₁
  let v₁ : A' →* E := (CentralPullback.first π r₁).comp e₁.equiv.toMonoidHom
  let u₂ : B' →* E := CentralPullback.first π l₂
  let v₂ : B' →* E := (CentralPullback.first π r₂).comp e₂.equiv.toMonoidHom
  have hu₁ : Function.Injective u₁ := CentralPullback.first_injective π l₁ hl₁
  have hv₁ : Function.Injective v₁ :=
    (CentralPullback.first_injective π r₁ hr₁).comp e₁.equiv.injective
  have hu₂ : Function.Injective u₂ := CentralPullback.first_injective π l₂ hl₂
  have hv₂ : Function.Injective v₂ :=
    (CentralPullback.first_injective π r₂ hr₂).comp e₂.equiv.injective
  let P := twoHNNPresentation G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  let T := twoHNNPresentation E A' B' u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂
  let D : HNNFamilyQuotient P T :=
    { vertex := π
      edge := fun b ↦ match b with
        | false => CentralPullback.second π l₁
        | true => CentralPullback.second π l₂
      left := by
        intro b
        cases b <;> apply MonoidHom.ext <;> intro x <;> exact x.property
      right := by
        intro b
        cases b
        · apply MonoidHom.ext
          intro x
          change π (CentralPullback.first π r₁ (e₁.equiv x)) =
            r₁ (CentralPullback.second π l₁ x)
          rw [show π (CentralPullback.first π r₁ (e₁.equiv x)) =
            r₁ (CentralPullback.second π r₁ (e₁.equiv x)) from (e₁.equiv x).property,
            e₁.second_equiv]
        · apply MonoidHom.ext
          intro x
          change π (CentralPullback.first π r₂ (e₂.equiv x)) =
            r₂ (CentralPullback.second π l₂ x)
          rw [show π (CentralPullback.first π r₂ (e₂.equiv x)) =
            r₂ (CentralPullback.second π r₂ (e₂.equiv x)) from (e₂.equiv x).property,
            e₂.second_equiv] }
  have hedge : ∀ b, Function.Surjective (D.edge b) := by
    intro b
    cases b
    · exact CentralPullback.second_surjective π l₁ hπ
    · exact CentralPullback.second_surjective π l₂ hπ
  have hkernel : ∀ (b : Bool) (z : D.vertex.ker), ∃ x : twoEdgeGroups A' B' b,
      twoLeft E A' B' u₁ u₂ b x = z ∧ twoRight E A' B' v₁ v₂ b x = z := by
    intro b z
    cases b
    · refine ⟨CentralPullback.kernelInclusion π l₁ z, rfl, ?_⟩
      change CentralPullback.first π r₁ (e₁.equiv (CentralPullback.kernelInclusion π l₁ z)) = z
      rw [e₁.kernel]
      rfl
    · refine ⟨CentralPullback.kernelInclusion π l₂ z, rfl, ?_⟩
      change CentralPullback.first π r₂ (e₂.equiv (CentralPullback.kernelInclusion π l₂ z)) = z
      rw [e₂.kernel]
      rfl
  refine ⟨TwoHNN E A' B' u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂, inferInstance, D.map, T.base,
    (D.map_ker_and_surjective hc hkernel hπ hedge).2,
    D.map_central hc hkernel hπ hedge, ?_, ?_⟩
  · exact (IdentifyingHNN.of_injective _ _ _ _).comp
      (IdentifyingHNN.of_injective u₁ v₁ hu₁ hv₁)
  · apply MonoidHom.ext
    intro e
    exact D.map_base e

end SmallPresentationStatements.Homology
