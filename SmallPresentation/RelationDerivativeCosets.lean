module

public import SmallPresentation.RelationDerivativeDirectSum

/-! Coset representatives give the independent translated factor summands in a
relation module. The representatives exist for every injective group homomorphism. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

open DirectSum
attribute [local instance] Classical.propDecidable

variable {G Q : Type} [Group G] [Group Q]

/-- Chosen left-coset representatives, expressed by their unique decomposition law. -/
structure CosetData (φ : G →* Q) where
  Index : Type
  representative : Index → Q
  bijective : Function.Bijective (fun z : Index × G ↦ representative z.1 * φ z.2)

/-- Every embedded subgroup has chosen coset representatives. -/
noncomputable def cosetDataOfInjective (φ : G →* Q) (hφ : Function.Injective φ) :
    CosetData φ := by
  let S : φ.range.LeftTransversal := default
  refine ⟨S.val, Subtype.val, ?_, ?_⟩
  · intro u v he
    have hpair := S.property.1
      (a₁ := (u.1, φ.rangeRestrict u.2)) (a₂ := (v.1, φ.rangeRestrict v.2)) he
    exact Prod.ext (congrArg (fun z : S.val × φ.range ↦ z.1) hpair)
      (hφ (congrArg (fun z : S.val × φ.range ↦ z.2.val) hpair))
  · intro g
    obtain ⟨⟨c, h⟩, he⟩ := S.property.2 g
    obtain ⟨x, hx⟩ := φ.rangeRestrict_surjective h
    exact ⟨(c, x), by simpa only [← hx, MonoidHom.coe_rangeRestrict] using he⟩

section Family

variable {A Q : Type} [Group Q]
  (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a)
  (q : FreeGroup (Σ a, X a) →* Q) (hq : Function.Surjective q)
  (φ : ∀ a, G a →* Q)
  (compat : ∀ a, q.comp (FreeGroup.map (Sigma.mk a)) = (φ a).comp (p a))
  (C : ∀ a, CosetData (φ a))

abbrev CosetIndex := Σ a, (C a).Index

noncomputable def cosetWord (i : CosetIndex G φ C) : FreeGroup (Σ a, X a) :=
  (sectionOfSurjective q hq).word ((C i.1).representative i.2)

@[simp] theorem cosetWord_projects (i : CosetIndex G φ C) :
    q (cosetWord X G q hq φ C i) = (C i.1).representative i.2 :=
  (sectionOfSurjective q hq).evaluates _

/-- The factor relation module at every chosen coset representative. -/
noncomputable def cosetRelationSum :
    (⨁ i : CosetIndex G φ C, Additive (Abelianization (p i.1).ker)) →+
      Additive (Abelianization q.ker) :=
  translatedRelationSum (fun i : CosetIndex G φ C ↦ X i.1)
    (fun i : CosetIndex G φ C ↦ G i.1) (fun i ↦ p i.1) q
    (fun i ↦ Sigma.mk i.1) (fun i ↦ φ i.1) (fun i ↦ compat i.1)
    (cosetWord X G q hq φ C)

@[simp] theorem cosetRelationSum_of (i : CosetIndex G φ C)
    (z : Additive (Abelianization (p i.1).ker)) :
    cosetRelationSum X G p q hq φ compat C (DirectSum.of _ i z) =
      relationConjugation q (cosetWord X G q hq φ C i)
        (relationMap (p i.1) q (Sigma.mk i.1) (φ i.1) (compat i.1) z) := by
  unfold cosetRelationSum translatedRelationSum
  erw [DirectSum.toAddMonoid_of]
  rfl

include C in
/-- Distinct factor-coset coordinates label disjoint Cayley edges. -/
theorem cosetEdges_injective : Function.Injective
    (translatedEdge (fun i : CosetIndex G φ C ↦ X i.1)
      (fun i : CosetIndex G φ C ↦ G i.1) q (fun i ↦ Sigma.mk i.1)
      (fun i ↦ φ i.1) (cosetWord X G q hq φ C)) := by
  rintro ⟨⟨a, c⟩, g, x⟩ ⟨⟨b, d⟩, h, y⟩ he
  have hletters : (⟨a, x⟩ : Σ a, X a) = ⟨b, y⟩ := congrArg Prod.snd he
  obtain ⟨hab, hxy⟩ := Sigma.mk.inj_iff.mp hletters
  cases hab
  cases hxy
  have hv : (C a).representative c * φ a g = (C a).representative d * φ a h := by
    simpa only [translatedEdge, cosetWord_projects] using congrArg Prod.fst he
  have hcg : (c, g) = (d, h) := (C a).bijective.1 hv
  have hc := congrArg Prod.fst hcg
  have hg := congrArg Prod.snd hcg
  cases hc
  cases hg
  rfl

/-- All coset translates of all factor relation modules form an independent sum. -/
theorem cosetRelationSum_injective (hp : ∀ a, Function.Surjective (p a)) :
    Function.Injective (cosetRelationSum X G p q hq φ compat C) :=
  translatedRelationSum_injective _ _ _ _ _ _ _ _ (fun i ↦ hp i.1)
    (cosetEdges_injective X G q hq φ C)

/-- An explicit coset decomposition computes the image of a conjugated factor class. -/
theorem cosetRelationSum_of_conjugation (a : A) (c : (C a).Index)
    (v : FreeGroup (X a)) (w : FreeGroup (Σ a, X a))
    (hw : q w = (C a).representative c * φ a (p a v))
    (z : Additive (Abelianization (p a).ker)) :
    cosetRelationSum X G p q hq φ compat C
      (DirectSum.of _ (⟨a, c⟩ : CosetIndex G φ C) (relationConjugation (p a) v z)) =
      relationConjugation q w (relationMap (p a) q (Sigma.mk a) (φ a) (compat a) z) := by
  apply relationDerivative_injective q hq
  rw [cosetRelationSum_of]
  simp only [relationDerivative_conjugation, relationDerivative_natural, chainMap_shift,
    cosetWord_projects, ← shift_mul, hw]

/-- Every ambient conjugate of a factor relation belongs to the coset sum. -/
theorem conjugated_factor_mem_cosetRelationSum_range
    (hp : ∀ a, Function.Surjective (p a)) (a : A)
    (w : FreeGroup (Σ a, X a)) (z : Additive (Abelianization (p a).ker)) :
    relationConjugation q w (relationMap (p a) q (Sigma.mk a) (φ a) (compat a) z) ∈
      (cosetRelationSum X G p q hq φ compat C).range := by
  obtain ⟨⟨c, g⟩, hcg⟩ := (C a).bijective.2 (q w)
  obtain ⟨v, hv⟩ := hp a g
  refine ⟨DirectSum.of _ (⟨a, c⟩ : CosetIndex G φ C) (relationConjugation (p a) v z), ?_⟩
  apply relationDerivative_injective q hq
  change relationDerivative q (translatedRelationSum _ _ _ _ _ _ _ _ _) = _
  unfold translatedRelationSum
  erw [DirectSum.toAddMonoid_of]
  simp only [translatedRelationMap, AddMonoidHom.comp_apply,
    relationDerivative_conjugation, relationDerivative_natural, chainMap_shift,
    cosetWord_projects, hv, ← shift_mul, hcg]

/-- The coset sum has exactly the image generated by all conjugated factor modules. -/
theorem cosetRelationSum_range (hp : ∀ a, Function.Surjective (p a)) :
    (cosetRelationSum X G p q hq φ compat C).range =
      ⨆ (a : A) (w : FreeGroup (Σ a, X a)),
        ((relationConjugation q w).comp
          (relationMap (p a) q (Sigma.mk a) (φ a) (compat a))).range := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using DirectSum.induction_on with
    | zero => exact AddSubgroup.zero_mem _
    | of i z =>
      rw [cosetRelationSum_of]
      exact AddSubgroup.mem_iSup_of_mem i.1
        (AddSubgroup.mem_iSup_of_mem (cosetWord X G q hq φ C i) ⟨z, rfl⟩)
    | add z t hz ht =>
      rw [map_add]
      exact AddSubgroup.add_mem _ hz ht
  · apply iSup_le
    intro a
    apply iSup_le
    intro w
    rintro _ ⟨z, rfl⟩
    exact conjugated_factor_mem_cosetRelationSum_range X G p q hq φ compat C hp a w z


end Family

end SmallPresentationStatements.RelationDerivative
