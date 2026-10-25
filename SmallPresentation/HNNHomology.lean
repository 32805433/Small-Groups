module

public import SmallPresentation.HNNSchurSurjectivity
public import SmallPresentation.HNNSchurKernel

/-!
# Proved degree-two homology of two HNN identifications

The edge abelianizations are projective, so equal Hopf obstructions identify
pullback central extensions. The vertex abelianization is projective and the
actual degree-one boundary has a left inverse, so central defects can be
corrected and the vertex map is onto on H₂. These hypotheses give the precise
cokernel statement needed by mitosis, without assuming Mayer--Vietoris.
The unrestricted Mayer--Vietoris sequence is not asserted here.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G A B : Type) [Group G] [Group A] [Group B]
variable (l₁ r₁ : A →* G) (l₂ r₂ : B →* G)
variable (hl₁ : Function.Injective l₁) (hr₁ : Function.Injective r₁)
    (hl₂ : Function.Injective l₂) (hr₂ : Function.Injective r₂)
variable [Module.Projective ℤ (H₁ G)] [Module.Projective ℤ (H₁ A)]
    [Module.Projective ℤ (H₁ B)]

/-- The degree-two cokernel formula for two HNN identifications, with the
canonical vertex and edge maps and explicit reusable sufficient hypotheses. -/
theorem twoHNN_degree_two_of_split_boundary
    (s : H₁ G →+ H₁ A × H₁ B)
    (hs : s.comp (edge₁ G A B l₁ r₁ l₂ r₂) = AddMonoidHom.id _) :
    Function.Surjective (map₂ (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂)) ∧
      (map₂ (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂)).ker =
        (edge₂ G A B l₁ r₁ l₂ r₂).range := by
  let P := twoHNNPresentation G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂
  let e := boolDirectSumEquiv (fun b ↦ H₁ (twoEdgeGroups A B b))
  let s' := e.symm.toAddMonoidHom.comp s
  have hs' : s'.comp (HNNFamilyPresentation.boundary₁
      (l := twoLeft G A B l₁ l₂) (r := twoRight G A B r₁ r₂)) = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro x
    rw [two_boundary₁]
    change e.symm (s (edge₁ G A B l₁ r₁ l₂ r₂ (e x))) = x
    rw [show s (edge₁ G A B l₁ r₁ l₂ r₂ (e x)) = e x from DFunLike.congr_fun hs (e x)]
    exact e.symm_apply_apply x
  exact ⟨P.map₂_base_surjective_of_split_boundary s' hs',
    twoHNN_schur_ker l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂⟩

/-- Under a split degree-one boundary, the connecting map is zero and the
three degree-two exactness identities all follow from the proved cokernel formula. -/
theorem twoHNN_exact_of_split_boundary
    (s : H₁ G →+ H₁ A × H₁ B)
    (hs : s.comp (edge₁ G A B l₁ r₁ l₂ r₂) = AddMonoidHom.id _) :
    ∃ d : H₂ (TwoHNN G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂) →+ H₁ A × H₁ B,
      (map₂ (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂)).ker =
        (edge₂ G A B l₁ r₁ l₂ r₂).range ∧
      (map₂ (twoBase G A B l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂)).range = d.ker ∧
      d.range = (edge₁ G A B l₁ r₁ l₂ r₂).ker := by
  obtain ⟨hsurj, hker⟩ := twoHNN_degree_two_of_split_boundary G A B
    l₁ r₁ l₂ r₂ hl₁ hr₁ hl₂ hr₂ s hs
  have hinj : Function.Injective (edge₁ G A B l₁ r₁ l₂ r₂) := by
    intro x y hxy
    have h := congrArg s hxy
    simpa only [← AddMonoidHom.comp_apply, hs, AddMonoidHom.id_apply] using h
  refine ⟨0, hker, ?_, ?_⟩
  · rw [AddMonoidHom.range_eq_top.mpr hsurj, AddMonoidHom.ker_zero]
  · rw [AddMonoidHom.range_zero, (AddMonoidHom.ker_eq_bot_iff _).mpr hinj]

end SmallPresentationStatements.Homology
