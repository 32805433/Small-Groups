module

public import SmallPresentation.Homology
public import Mathlib.Tactic.Abel

/-! The canonical split part of degree-two product homology. This uses only
functoriality of the Hopf model; the identification of the remaining cross
effect with a tensor product is a separate theorem. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable {G H : Type} [Group G] [Group H]

@[simp] theorem schurMap_one (x : Schur G) : schurMap (1 : G →* H) x = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change totalMap _ _ _ (canonicalRelations_map (1 : G →* H)) x.1.1 = 1
  apply central_lifts_agree_on_commutator (RelationExtension.projection (canonicalRelations H))
    ((UniversalCentralExtension.central_iff _).mpr (RelationExtension.kernel_central _))
    (totalMap _ _ _ (canonicalRelations_map (1 : G →* H))) (1 : _ →* _)
  · apply MonoidHom.ext
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective _ z
    change QuotientGroup.mk' (canonicalRelations H) (FreeGroup.map (1 : G →* H) w) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    change freeProjection H (FreeGroup.map (1 : G →* H) w) = 1
    simpa using DFunLike.congr_fun (freeProjection_map (1 : G →* H)) w
  · exact x.1.property

@[simp] theorem map₂_one (x : H₂ G) : map₂ (1 : G →* H) x = 0 :=
  schurMap_one x

@[simp] theorem map₂_id (x : H₂ G) : map₂ (MonoidHom.id G) x = x := schurMap_id x

@[simp] theorem map₂_comp {K : Type} [Group K] (f : G →* H) (g : H →* K)
    (x : H₂ G) : map₂ g (map₂ f x) = map₂ (g.comp f) x := schurMap_comp f g x

variable (G H)

/-- Both canonical projections from product homology. -/
def productProjection : H₂ (G × H) →+ H₂ G × H₂ H :=
  (map₂ (MonoidHom.fst G H)).prod (map₂ (MonoidHom.snd G H))

/-- The canonical summand supplied by the two factor inclusions. -/
def productSection : H₂ G × H₂ H →+ H₂ (G × H) :=
  (map₂ (MonoidHom.inl G H)).coprod (map₂ (MonoidHom.inr G H))

@[simp] theorem productProjection_section (x : H₂ G × H₂ H) :
    productProjection G H (productSection G H x) = x := by
  rcases x with ⟨x,y⟩
  ext <;> simp [productProjection, productSection, map₂_comp]

/-- The genuinely mixed part of the Schur multiplier of a product. -/
abbrev ProductCrossEffect := (productProjection G H).ker

/-- Remove the two canonically split factor contributions. -/
def productRemainder : H₂ (G × H) →+ ProductCrossEffect G H :=
  (AddMonoidHom.id _ - (productSection G H).comp (productProjection G H)).codRestrict _ (by
    intro x
    change productProjection G H (x - productSection G H (productProjection G H x)) = 0
    simp)

/-- Canonical splitting for any two groups. The tensor-product theorem concerns
only the third summand and is not used in this construction. -/
def productSplit : H₂ (G × H) ≃+ (H₂ G × H₂ H) × ProductCrossEffect G H where
  toFun x := (productProjection G H x, productRemainder G H x)
  invFun x := productSection G H x.1 + x.2.1
  left_inv x := by simp [productRemainder]
  right_inv x := by
    rcases x with ⟨x,y⟩
    apply Prod.ext
    · change productProjection G H (productSection G H x + y.1) = x
      rw [map_add, productProjection_section, show productProjection G H y.1 = 0 from y.2,
        add_zero]
    · apply Subtype.ext
      change productSection G H x + y.1 - productSection G H
        (productProjection G H (productSection G H x + y.1)) = y.1
      rw [map_add, productProjection_section, show productProjection G H y.1 = 0 from y.2,
        add_zero]
      abel
  map_add' x y := by exact Prod.ext (map_add _ x y) (map_add _ x y)

@[simp] theorem productRemainder_section (x : H₂ G × H₂ H) :
    productRemainder G H (productSection G H x) = 0 := by
  apply Subtype.ext
  change productSection G H x - productSection G H
    (productProjection G H (productSection G H x)) = 0
  simp

@[simp] theorem productSplit_inl (x : H₂ G) :
    productSplit G H (map₂ (MonoidHom.inl G H) x) = ((x,0),0) := by
  have h : map₂ (MonoidHom.inl G H) x = productSection G H (x,0) := by
    simp [productSection]
  rw [h]
  exact Prod.ext (productProjection_section G H _) (productRemainder_section G H _)

@[simp] theorem productSplit_inr (x : H₂ H) :
    productSplit G H (map₂ (MonoidHom.inr G H) x) = ((0,x),0) := by
  have h : map₂ (MonoidHom.inr G H) x = productSection G H (0,x) := by
    simp [productSection]
  rw [h]
  exact Prod.ext (productProjection_section G H _) (productRemainder_section G H _)

end SmallPresentationStatements.Homology
