module

public import SmallPresentation.HNNSchurSurjectivity
public import SmallPresentation.HNNSchurKernel
public import SmallPresentation.HomologyAbelianization
public import SmallPresentation.MitosisModel

/-! The mitosis vertex map is onto on H₂ for projective source abelianization.
The proof uses central lifting and the explicit inverse of the degree-one
boundary, without assuming a general Mayer--Vietoris sequence. -/
@[expose] public section

namespace SmallPresentationStatements.MitosisModel

open Homology DirectSum

variable (J : Type) [Group J]

/-- The inverse of the actual mitosis degree-one edge boundary. -/
def homologyEdge₁LeftInverse : H₁ (J × J) →+ H₁ J × H₁ J :=
  (-(map₁ (MonoidHom.fst J J)) - map₁ (MonoidHom.snd J J)).prod
    (map₁ (MonoidHom.fst J J))

theorem homologyEdge₁LeftInverse_comp :
    (homologyEdge₁LeftInverse J).comp
      (Homology.edge₁ (J × J) J J (left J) (diagonal J) (left J) (right J)) =
        AddMonoidHom.id _ := by
  have hfl : (MonoidHom.fst J J).comp (left J) = MonoidHom.id J := rfl
  have hfr : (MonoidHom.fst J J).comp (right J) = 1 := rfl
  have hfd : (MonoidHom.fst J J).comp (diagonal J) = MonoidHom.id J := rfl
  have hsl : (MonoidHom.snd J J).comp (left J) = 1 := rfl
  have hsr : (MonoidHom.snd J J).comp (right J) = MonoidHom.id J := rfl
  have hsd : (MonoidHom.snd J J).comp (diagonal J) = MonoidHom.id J := rfl
  apply AddMonoidHom.ext
  intro x
  apply Prod.ext <;>
    simp [homologyEdge₁LeftInverse, Homology.edge₁, AddMonoidHom.comp_apply,
      AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.neg_apply, AddMonoidHom.id_apply, map_add, map_sub,
      map₁_comp, hfl, hfr, hfd, hsl, hsr, hsd, map₁_id, map₁_one]

/-- A substantive degree-two Mayer--Vietoris consequence, proved by central
extension lifting for every group with projective integral abelianization. -/
theorem homology_base₂_surjective [Module.Projective ℤ (H₁ J)] :
    Function.Surjective (map₂ (base J)) := by
  let := productH₁_projective J J
  let P := twoHNNPresentation (J × J) J J (left J) (diagonal J) (left J) (right J)
    (left_injective J) (diagonal_injective J) (left_injective J) (right_injective J)
  let e := boolDirectSumEquiv (fun b ↦ H₁ (twoEdgeGroups J J b))
  let s := e.symm.toAddMonoidHom.comp (homologyEdge₁LeftInverse J)
  have hs : s.comp (HNNFamilyPresentation.boundary₁
      (l := twoLeft (J × J) J J (left J) (left J))
      (r := twoRight (J × J) J J (diagonal J) (right J))) = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro x
    rw [two_boundary₁]
    change e.symm (homologyEdge₁LeftInverse J
      (Homology.edge₁ (J × J) J J (left J) (diagonal J) (left J) (right J) (e x))) = x
    rw [show homologyEdge₁LeftInverse J
        (Homology.edge₁ (J × J) J J (left J) (diagonal J) (left J) (right J) (e x)) = e x from
      DFunLike.congr_fun (homologyEdge₁LeftInverse_comp J) (e x)]
    exact e.symm_apply_apply x
  exact P.map₂_base_surjective_of_split_boundary s hs

/-- The full canonical kernel formula, obtained by retaining the central
obstruction quotient inside an actual HNN extension. -/
theorem homology_base₂_ker [Module.Projective ℤ (H₁ J)] :
    (map₂ (base J)).ker =
      (Homology.edge₂ (J × J) J J (left J) (diagonal J) (left J) (right J)).range :=
  twoHNN_schur_ker (left J) (diagonal J) (left J) (right J)
    (left_injective J) (diagonal_injective J) (left_injective J) (right_injective J)

/-- Both degree-two assertions needed for the mitosis Schur calculation,
proved algebraically for projective integral abelianization. -/
theorem homology_degree_two [Module.Projective ℤ (H₁ J)] :
    Function.Surjective (map₂ (base J)) ∧
      (map₂ (base J)).ker =
        (Homology.edge₂ (J × J) J J (left J) (diagonal J) (left J) (right J)).range :=
  ⟨homology_base₂_surjective J, homology_base₂_ker J⟩

end SmallPresentationStatements.MitosisModel
