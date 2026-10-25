module

public import SmallPresentation.Basic

/-! # Structural properties used by the small-presentation constructions -/
@[expose] public section

namespace SmallPresentationStatements

/-- Every central extension of the group admits a homomorphic section. -/
def CentrallyClosed (G : Type) [Group G] : Prop :=
  ∀ (E : Type) [Group E] (π : E →* G), Function.Surjective π →
    (∀ z ∈ π.ker, ∀ x : E, z * x = x * z) →
    ∃ σ : G →* E, π.comp σ = MonoidHom.id G

def Noncyclic (G : Type) [Group G] : Prop :=
  ¬ ∃ g : G, ∀ x : G, ∃ k : ℤ, g ^ k = x

end SmallPresentationStatements
