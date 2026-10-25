module

public import SmallPresentation.Kunneth
public import SmallPresentation.HNNHomology
public import SmallPresentation.MitosisHomology
public import SmallPresentation.MitosisAbelianization
public import SmallPresentation.MitosisHNNHomology

/-! The finite-mitosis Schur multiplier is calculated from proved natural
Künneth and central-extension theorems. Projectivity of the source abelianization
is explicit; finite double mitosis satisfies it through free abelianization. -/
@[expose] public section

namespace SmallPresentationStatements.MitosisModel

open Homology

variable (J : Type) [Group J]

theorem homology_edge₁_injective :
    Function.Injective (Homology.edge₁ (J × J) J J (left J) (diagonal J) (left J) (right J)) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have hf := congrArg (map₁ (MonoidHom.fst J J)) hx
  have hs := congrArg (map₁ (MonoidHom.snd J J)) hx
  have hfl : (MonoidHom.fst J J).comp (left J) = MonoidHom.id J := rfl
  have hfr : (MonoidHom.fst J J).comp (right J) = 1 := rfl
  have hfd : (MonoidHom.fst J J).comp (diagonal J) = MonoidHom.id J := rfl
  have hsl : (MonoidHom.snd J J).comp (left J) = 1 := rfl
  have hsr : (MonoidHom.snd J J).comp (right J) = MonoidHom.id J := rfl
  have hsd : (MonoidHom.snd J J).comp (diagonal J) = MonoidHom.id J := rfl
  change map₁ (MonoidHom.fst J J) (Homology.edge₁ _ _ _ _ _ _ _ x) = _ at hf
  change map₁ (MonoidHom.snd J J) (Homology.edge₁ _ _ _ _ _ _ _ x) = _ at hs
  simp only [Homology.edge₁, AddMonoidHom.coprod_apply, AddMonoidHom.sub_apply,
    map_add, map_sub, map_zero, map₁_comp, hfl,hfr,hfd,hsl,hsr,hsd,map₁_id,map₁_one] at hf hs
  have hx₂ : x.2 = 0 := by simpa using hf
  have hx₁ : x.1 = 0 := by simpa [hx₂] using hs
  exact Prod.ext hx₁ hx₂

/-- The canonical Künneth coordinates and exact vertex-map kernel determine
the mitosis Schur multiplier. All coordinate algebra is independent of how
the two exactness assertions were proved. -/
theorem schur_tensor_equiv_of_exact
    (hmv : Function.Surjective (map₂ (base J)) ∧
      (map₂ (base J)).ker =
        (Homology.edge₂ (J × J) J J (left J) (diagonal J) (left J) (right J)).range) :
    Nonempty (H₂ (Model J) ≃+ TensorProduct ℤ (H₁ J) (H₁ J)) := by
  obtain ⟨e,δ,hl,hr,hd⟩ := kunneth_square J
  let q : H₂ J × H₂ J × TensorProduct ℤ (H₁ J) (H₁ J) →+ H₂ (Model J) :=
    (map₂ (base J)).comp e.symm.toAddMonoidHom
  have he (x : H₂ J × H₂ J) :
      e (Homology.edge₂ (J × J) J J (left J) (diagonal J) (left J) (right J) x) =
        MitosisHomology.edge₂ δ x := by
    change e ((map₂ (left J) x.1 - map₂ (diagonal J) x.1) +
      (map₂ (left J) x.2 - map₂ (right J) x.2)) = _
    rw [map_add, map_sub, map_sub]
    change (e (map₂ (MonoidHom.inl J J) x.1) -
        e (map₂ ((MonoidHom.id J).prod (MonoidHom.id J)) x.1)) +
      (e (map₂ (MonoidHom.inl J J) x.2) - e (map₂ (MonoidHom.inr J J) x.2)) = _
    rw [hl,hd,hl,hr]
    apply Prod.ext
    · change (x.1 - x.1) + (x.2 - 0) = x.2
      abel
    · apply Prod.ext
      · change (0 - x.1) + (0 - x.2) = -x.1 - x.2
        abel
      · change (0 - δ x.1) + (0 - 0) = -δ x.1
        abel
  have hq : q.ker = (MitosisHomology.edge₂ δ).range := by
    ext x
    constructor
    · intro hx
      have hx' : e.symm x ∈ (Homology.edge₂ (J × J) J J (left J) (diagonal J) (left J) (right J)).range := by
        rw [← hmv.2]
        exact hx
      obtain ⟨y,hy⟩ := hx'
      refine ⟨y, ?_⟩
      rw [← he, hy, e.apply_symm_apply]
    · rintro ⟨y,rfl⟩
      change map₂ (base J) (e.symm (MitosisHomology.edge₂ δ y)) = 0
      rw [← he, e.symm_apply_apply]
      change Homology.edge₂ _ _ _ _ _ _ _ y ∈ (map₂ (base J)).ker
      rw [hmv.2]
      exact ⟨y,rfl⟩
  have hsurj : Function.Surjective q := hmv.1.comp e.symm.surjective
  let d : H₂ (Model J) →+ H₁ J × H₁ J := 0
  exact ⟨MitosisHomology.secondHomologyEquiv δ q d hq
    (by rw [AddMonoidHom.range_eq_top.mpr hsurj]; simp [d]) (by simp [d])⟩

/-- The mitosis Schur multiplier, proved for every group with projective
integral abelianization. No Mayer--Vietoris admission is used. -/
theorem schur_tensor_equiv [Module.Projective ℤ (H₁ J)] :
    Nonempty (H₂ (Model J) ≃+ TensorProduct ℤ (H₁ J) (H₁ J)) :=
  schur_tensor_equiv_of_exact J (homology_degree_two J)

theorem schur_torsionFree [Module.Free ℤ (H₁ J)] :
    IsMulTorsionFree (Schur (Model J)) := by
  let : Module.Free ℤ (TensorProduct ℤ (H₁ J) (H₁ J)) := Module.Free.tensor (R := ℤ) (S := ℤ)
  let : HasUniqueDiv (TensorProduct ℤ (H₁ J) (H₁ J)) :=
    HasUniqueDiv.of_isTorsionFree ℤ _
  obtain ⟨e⟩ := schur_tensor_equiv J
  exact e.toMultiplicative.injective.isMulTorsionFree e.toMultiplicative.toMonoidHom

theorem finite_h₁_free {n r : ℕ} (P : FP n r) : Module.Free ℤ (H₁ (MitosisWords.presentation P).Group) := by
  let e : H₁ (MitosisWords.presentation P).Group ≃+ FreeAbelianGroup (Fin 2) :=
    (abelianizationFreeEquiv P).toAdditive
  exact Module.Free.of_equiv e.symm.toIntLinearEquiv

/-- Two actual finite mitoses have torsion-free Schur multiplier, independently
of the seed's Schur multiplier or abelianization. -/
theorem finite_double_schur_torsionFree {n r : ℕ} (P : FP n r) :
    IsMulTorsionFree (Schur (MitosisWords.presentation (MitosisWords.presentation P)).Group) := by
  let := finite_h₁_free P
  let := schur_torsionFree (MitosisWords.presentation P).Group
  let e := schurEquiv (presentationEquiv (MitosisWords.presentation P))
  exact e.injective.isMulTorsionFree e.toMonoidHom

end SmallPresentationStatements.MitosisModel
