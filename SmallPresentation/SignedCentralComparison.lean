module

public import SmallPresentation.SignedTietze
public import SmallPresentation.RelativeRelationModule

/-! Comparison of the central relation extensions before and after eliminating
the perfect, centrally closed source factors from the relative signed presentation. -/
@[expose] public section

namespace SmallPresentationStatements.CentralRelationMap

open scoped commutatorElement

variable {F E B : Type} [Group F] [Group E] [Group B]
    (N : Subgroup F) [N.Normal] (π : E →* B)
    (hc : ∀ z ∈ π.ker, ∀ x : E, z * x = x * z)
    (f : F →* E) (hf : N ≤ (π.comp f).ker)

def descend : RelationExtension.Total N →* E :=
  QuotientGroup.lift (RelationExtension.commutatorKernel N) f (by
    apply Subgroup.commutator_le.mpr
    intro n hn x _
    change f ⁅n, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc (f n) (hf hn) (f x))

@[simp] theorem descend_mk (x : F) :
    descend N π hc f hf (QuotientGroup.mk' (RelationExtension.commutatorKernel N) x) = f x := rfl

end SmallPresentationStatements.CentralRelationMap

namespace SmallPresentationStatements.SignedCoding.CentralComparison

open Word

variable {L d : ℕ} (Q : FP 2 L)

abbrev RelativeRelations := RelativeSmallCancellation.relatorSubgroup
  (Relative.FactorGroup Q (d := d)) Relative.rowLength (Relative.rows Q)

abbrev RelativeTotal := RelationExtension.Total (RelativeRelations Q (d := d))

def relativeMk : Relative.FreeProduct Q (d := d) →* RelativeTotal Q (d := d) :=
  QuotientGroup.mk' _

def relativeProjection : RelativeTotal Q (d := d) →* CodedGroup Q d :=
  (Relative.relativeToCoded Q).comp (RelationExtension.projection (RelativeRelations Q))

@[simp] theorem relativeProjection_mk (x : Relative.FreeProduct Q (d := d)) :
    relativeProjection Q (relativeMk Q x) = Relative.freeToCoded Q x := rfl

theorem relativeProjection_central :
    ∀ z ∈ (relativeProjection Q (d := d)).ker, ∀ x, z * x = x * z := by
  intro z hz x
  apply RelationExtension.kernel_central (RelativeRelations Q) z _ x
  apply (Relative.equivCodedGroup Q).injective
  exact hz.trans (map_one _).symm

def relativeVertex (v : Fin d) : RelativeTotal Q (d := d) := relativeMk Q (Relative.freeVertex Q v)

def relativeSource (a : Relative.Pair d) : Q.Group →* RelativeTotal Q (d := d) :=
  (relativeMk Q).comp (Relative.freeSource Q a)

@[simp] theorem relativeProjection_vertex (v : Fin d) :
    relativeProjection Q (relativeVertex Q v) = PresentedGroup.of v := by
  simp [relativeVertex]

@[simp] theorem relativeProjection_source (a : Relative.Pair d) (x : Q.Group) :
    relativeProjection Q (relativeSource Q a x) = sourceHom Q a.val.1 a.val.2 a.property x := by
  simp [relativeSource]

def originalMk : FreeGroup (Fin d) →* CentralGroup Q d :=
  QuotientGroup.mk' _

def originalVertex (v : Fin d) : CentralGroup Q d := originalMk Q (FreeGroup.of v)

@[simp] theorem originalProjection_vertex (v : Fin d) :
    centralProjection Q d (originalVertex Q v) = PresentedGroup.of v := rfl

def verticesToRelative : FreeGroup (Fin d) →* RelativeTotal Q (d := d) := FreeGroup.lift (relativeVertex Q)

theorem verticesToRelative_projects :
    (relativeProjection Q).comp (verticesToRelative Q (d := d)) = PresentedGroup.mk (relators Q d) := by
  apply FreeGroup.ext_hom
  intro v
  simp [verticesToRelative]
  rfl

def toRelative : CentralGroup Q d →* RelativeTotal Q (d := d) :=
  CentralRelationMap.descend (relationSubgroup Q d) (relativeProjection Q)
    (relativeProjection_central Q) (verticesToRelative Q) (by
      intro x hx
      change relativeProjection Q (verticesToRelative Q x) = 1
      rw [show relativeProjection Q (verticesToRelative Q x) = PresentedGroup.mk (relators Q d) x
        from DFunLike.congr_fun (verticesToRelative_projects Q) x]
      exact (QuotientGroup.eq_one_iff x).mpr hx)

@[simp] theorem toRelative_mk (x : FreeGroup (Fin d)) :
    toRelative Q (originalMk Q x) = verticesToRelative Q x := rfl

@[simp] theorem toRelative_vertex (v : Fin d) :
    toRelative Q (originalVertex Q v) = relativeVertex Q v := FreeGroup.lift_apply_of

theorem toRelative_projects : (relativeProjection Q).comp (toRelative Q (d := d)) =
    centralProjection Q d := by
  apply MonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (RelationExtension.commutatorKernel (relationSubgroup Q d)) z
  exact DFunLike.congr_fun (verticesToRelative_projects Q) x

variable (hC : CentrallyClosed Q.Group)

noncomputable def originalSource (a : Relative.Pair d) : Q.Group →* CentralGroup Q d :=
  Classical.choose (RelationExtension.lift (relationSubgroup Q d) hC
    (sourceHom Q a.val.1 a.val.2 a.property))

theorem originalSource_projects (a : Relative.Pair d) :
    (centralProjection Q d).comp (originalSource Q hC a) = sourceHom Q a.val.1 a.val.2 a.property :=
  Classical.choose_spec (RelationExtension.lift (relationSubgroup Q d) hC
    (sourceHom Q a.val.1 a.val.2 a.property))

noncomputable def factorsToOriginal : ∀ a : Relative.Factor d,
    Relative.FactorGroup Q a →* CentralGroup Q d
  | .inl a => originalSource Q hC a
  | .inr v => zpowersHom _ (originalVertex Q v)

noncomputable def freeToOriginal : Relative.FreeProduct Q (d := d) →* CentralGroup Q d :=
  Monoid.CoprodI.lift (factorsToOriginal Q hC)

@[simp] theorem freeToOriginal_vertex (v : Fin d) :
    freeToOriginal Q hC (Relative.freeVertex Q v) = originalVertex Q v := by
  simp [freeToOriginal, factorsToOriginal, Relative.freeVertex]

@[simp] theorem freeToOriginal_source (a : Relative.Pair d) (x : Q.Group) :
    freeToOriginal Q hC (Relative.freeSource Q a x) = originalSource Q hC a x :=
  Monoid.CoprodI.lift_of _ _

theorem freeToOriginal_projects : (centralProjection Q d).comp (freeToOriginal Q hC) =
    Relative.freeToCoded Q (d := d) := by
  apply Monoid.CoprodI.ext_hom
  intro a
  cases a with
  | inl a =>
    apply MonoidHom.ext
    intro x
    exact DFunLike.congr_fun (originalSource_projects Q hC a) x
  | inr v =>
    apply MonoidHom.ext_mint
    simp [freeToOriginal, factorsToOriginal, Relative.freeToCoded, Relative.factorsToCoded]

noncomputable def fromRelative : RelativeTotal Q (d := d) →* CentralGroup Q d :=
  CentralRelationMap.descend (RelativeRelations Q) (centralProjection Q d)
    (RelationExtension.kernel_central _) (freeToOriginal Q hC) (by
      rw [freeToOriginal_projects]
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨a, rfl⟩
      exact Relative.freeToCoded_kills_rows Q a)

@[simp] theorem fromRelative_mk (x : Relative.FreeProduct Q (d := d)) :
    fromRelative Q hC (relativeMk Q x) = freeToOriginal Q hC x := rfl

@[simp] theorem fromRelative_vertex (v : Fin d) :
    fromRelative Q hC (relativeVertex Q v) = originalVertex Q v := by
  simp [relativeVertex]

@[simp] theorem fromRelative_source (a : Relative.Pair d) (x : Q.Group) :
    fromRelative Q hC (relativeSource Q a x) = originalSource Q hC a x := by
  simp [relativeSource]

theorem fromRelative_projects : (centralProjection Q d).comp (fromRelative Q hC) =
    relativeProjection Q (d := d) := by
  apply MonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (RelationExtension.commutatorKernel (RelativeRelations Q (d := d))) z
  exact DFunLike.congr_fun (freeToOriginal_projects Q hC) x

theorem from_to : (fromRelative Q hC).comp (toRelative Q (d := d)) = MonoidHom.id _ := by
  have h : ((fromRelative Q hC).comp (toRelative Q)).comp (originalMk Q (d := d)) = originalMk Q := by
    apply FreeGroup.ext_hom
    intro v
    change fromRelative Q hC (toRelative Q (originalVertex Q v)) = originalVertex Q v
    simp
  apply MonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (RelationExtension.commutatorKernel (relationSubgroup Q d)) z
  exact DFunLike.congr_fun h x

variable (hperfect : commutator Q.Group = ⊤)

include hperfect in
theorem toRelative_originalSource (a : Relative.Pair d) :
    (toRelative Q).comp (originalSource Q hC a) = relativeSource Q a := by
  apply UniversalCentralExtension.lift_unique (relativeProjection Q)
    ((UniversalCentralExtension.central_iff _).mpr (relativeProjection_central Q)) hperfect
  apply MonoidHom.ext
  intro x
  have h := DFunLike.congr_fun (toRelative_projects Q) (originalSource Q hC a x)
  simp only [MonoidHom.comp_apply] at h
  change relativeProjection Q (toRelative Q (originalSource Q hC a x)) =
    relativeProjection Q (relativeSource Q a x)
  rw [h, relativeProjection_source]
  exact DFunLike.congr_fun (originalSource_projects Q hC a) x

include hperfect in
theorem to_from : (toRelative Q (d := d)).comp (fromRelative Q hC) = MonoidHom.id _ := by
  have h : ((toRelative Q).comp (fromRelative Q hC)).comp (relativeMk Q (d := d)) = relativeMk Q := by
    apply Monoid.CoprodI.ext_hom
    intro a
    cases a with
    | inl a =>
      apply MonoidHom.ext
      intro x
      change toRelative Q (fromRelative Q hC (relativeSource Q a x)) = relativeSource Q a x
      rw [fromRelative_source]
      exact DFunLike.congr_fun (toRelative_originalSource Q hC hperfect a) x
    | inr v =>
      apply MonoidHom.ext_mint
      change toRelative Q (fromRelative Q hC (relativeVertex Q v)) = relativeVertex Q v
      simp
  apply MonoidHom.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (RelationExtension.commutatorKernel (RelativeRelations Q (d := d))) z
  exact DFunLike.congr_fun h x

noncomputable def totalEquiv : CentralGroup Q d ≃* RelativeTotal Q (d := d) where
  toFun := toRelative Q
  invFun := fromRelative Q hC
  left_inv x := DFunLike.congr_fun (from_to Q hC) x
  right_inv x := DFunLike.congr_fun (to_from Q hC hperfect) x
  map_mul' := (toRelative Q).map_mul

noncomputable def kernelEquiv : RelationExtension.Kernel (relationSubgroup Q d) ≃*
    RelationExtension.Kernel (RelativeRelations Q (d := d)) where
  toFun x := ⟨toRelative Q x.val, by
    apply (Relative.equivCodedGroup Q).injective
    change relativeProjection Q (toRelative Q x.val) = Relative.relativeToCoded Q 1
    rw [map_one]
    exact (DFunLike.congr_fun (toRelative_projects Q) x.val).trans x.property⟩
  invFun x := ⟨fromRelative Q hC x.val, by
    change centralProjection Q d (fromRelative Q hC x.val) = 1
    rw [show centralProjection Q d (fromRelative Q hC x.val) = relativeProjection Q x.val
      from DFunLike.congr_fun (fromRelative_projects Q hC) x.val]
    change Relative.relativeToCoded Q (RelationExtension.projection (RelativeRelations Q) x.val) = 1
    rw [show RelationExtension.projection (RelativeRelations Q) x.val = 1 from x.property, map_one]⟩
  left_inv x := Subtype.ext (DFunLike.congr_fun (from_to Q hC) x.val)
  right_inv x := Subtype.ext (DFunLike.congr_fun (to_from Q hC hperfect) x.val)
  map_mul' x y := Subtype.ext ((toRelative Q).map_mul x.val y.val)

end SmallPresentationStatements.SignedCoding.CentralComparison
