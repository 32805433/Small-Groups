module

public import SmallPresentation.HomologyConjugation
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# HNN presentations with an arbitrary family of stable letters

The presentation is specified by its universal property. No homology conclusions
are fields of this structure. The edge groups need not be finite in number, and
the degree-one calculation does not require injective attaching maps.
-/
@[expose] public section

namespace SmallPresentationStatements.Homology

open DirectSum

variable {I G K : Type} {A : I → Type} [Group G] [Group K] [∀ i, Group (A i)]

/-- The universal property of a simultaneous HNN presentation. -/
structure HNNFamilyPresentation (l r : ∀ i, A i →* G) (K : Type) [Group K] where
  base : G →* K
  stable : I → K
  conjugates : ∀ i a, (stable i)⁻¹ * base (l i a) * stable i = base (r i a)
  lift : ∀ {H : Type} [Group H] (f : G →* H) (t : I → H),
    (∀ i a, (t i)⁻¹ * f (l i a) * t i = f (r i a)) → K →* H
  lift_base : ∀ {H : Type} [Group H] (f : G →* H) (t : I → H)
    (h : ∀ i a, (t i)⁻¹ * f (l i a) * t i = f (r i a)) (g : G),
    lift f t h (base g) = f g
  lift_stable : ∀ {H : Type} [Group H] (f : G →* H) (t : I → H)
    (h : ∀ i a, (t i)⁻¹ * f (l i a) * t i = f (r i a)) (i : I),
    lift f t h (stable i) = t i
  hom_ext : ∀ {H : Type} [Group H] (f g : K →* H),
    (∀ x, f (base x) = g (base x)) →
    (∀ i, f (stable i) = g (stable i)) → f = g

namespace HNNFamilyPresentation

variable {l r : ∀ i, A i →* G} (P : HNNFamilyPresentation l r K)
variable [DecidableEq I]

/-- The degree-one edge boundary for any family of attaching maps. -/
noncomputable def boundary₁ : (⨁ i, H₁ (A i)) →+ H₁ G :=
  DirectSum.toAddMonoid fun i ↦ map₁ (l i) - map₁ (r i)

/-- The degree-two edge boundary, using the canonical Hopf maps. -/
noncomputable def boundary₂ : (⨁ i, H₂ (A i)) →+ H₂ G :=
  DirectSum.toAddMonoid fun i ↦ map₂ (l i) - map₂ (r i)

@[simp] theorem boundary₁_of (i : I) (x : H₁ (A i)) :
    boundary₁ (l := l) (r := r) (DirectSum.of _ i x) = map₁ (l i) x - map₁ (r i) x := by
  classical
  simp [boundary₁]

@[simp] theorem boundary₂_of (i : I) (x : H₂ (A i)) :
    boundary₂ (l := l) (r := r) (DirectSum.of _ i x) = map₂ (l i) x - map₂ (r i) x := by
  classical
  simp [boundary₂]

omit [DecidableEq I] in
theorem abelianization_conjugates (i : I) (a : A i) :
    Abelianization.of (P.base (l i a)) = Abelianization.of (P.base (r i a)) := by
  have h := congrArg Abelianization.of (P.conjugates i a)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

omit [DecidableEq I] in
theorem map₁_base_left_eq_right (i : I) (x : H₁ (A i)) :
    map₁ P.base (map₁ (l i) x) = map₁ P.base (map₁ (r i) x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator (A i)) x.toMul
  exact P.abelianization_conjugates i a

/-- The degree-one boundary followed by the vertex map is zero. -/
theorem map₁_base_boundary₁ : (map₁ P.base).comp (boundary₁ (l := l) (r := r)) = 0 := by
  classical
  apply DirectSum.addHom_ext
  intro i x
  change map₁ P.base (boundary₁ (l := l) (r := r) (DirectSum.of _ i x)) = 0
  rw [boundary₁_of, map_sub, P.map₁_base_left_eq_right, sub_self]

omit [DecidableEq I] in
theorem map₂_base_left_eq_right (i : I) (x : H₂ (A i)) :
    map₂ P.base (map₂ (l i) x) = map₂ P.base (map₂ (r i) x) := by
  have h := map₂_eq_of_conjugate (P.base.comp (l i)) (P.base.comp (r i))
    (P.stable i)⁻¹ (by intro a; simpa only [inv_inv, MonoidHom.comp_apply] using P.conjugates i a)
  change schurMap P.base (schurMap (l i) x.toMul) =
    schurMap P.base (schurMap (r i) x.toMul)
  rw [schurMap_comp, schurMap_comp]
  exact DFunLike.congr_fun h x

/-- Conjugation invariance proves that the degree-two boundary is a cycle. -/
theorem map₂_base_boundary₂ : (map₂ P.base).comp (boundary₂ (l := l) (r := r)) = 0 := by
  classical
  apply DirectSum.addHom_ext
  intro i x
  change map₂ P.base (boundary₂ (l := l) (r := r) (DirectSum.of _ i x)) = 0
  rw [boundary₂_of, map_sub, P.map₂_base_left_eq_right, sub_self]

variable {C : Type} [AddCommGroup C]

/-- Extend an additive map from the vertex abelianization and arbitrary stable-letter values. -/
noncomputable def lift₁ (f : H₁ G →+ C) (t : I → C)
    (h : ∀ i x, f (map₁ (l i) x) = f (map₁ (r i) x)) : H₁ K →+ C :=
  (Abelianization.lift (P.lift (f.toMultiplicativeRight.comp Abelianization.of)
    (fun i ↦ Multiplicative.ofAdd (t i)) (by
      intro i a
      change Multiplicative.ofAdd (-t i + f (Additive.ofMul (Abelianization.of (l i a))) + t i) =
        Multiplicative.ofAdd (f (Additive.ofMul (Abelianization.of (r i a))))
      have hh := h i (Additive.ofMul (Abelianization.of a))
      change f (Additive.ofMul (Abelianization.of (l i a))) =
        f (Additive.ofMul (Abelianization.of (r i a))) at hh
      rw [hh]
      congr 1
      simp [add_comm]))).toAdditiveLeft

omit [DecidableEq I] in
@[simp] theorem lift₁_base (f : H₁ G →+ C) (t : I → C)
    (h : ∀ i x, f (map₁ (l i) x) = f (map₁ (r i) x)) (x : H₁ G) :
    P.lift₁ f t h (map₁ P.base x) = f x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator G) x.toMul
  change P.lift₁ f t h (Additive.ofMul (Abelianization.of (P.base a))) =
    f (Additive.ofMul (Abelianization.of a))
  simp [lift₁, P.lift_base]

omit [DecidableEq I] in
@[simp] theorem lift₁_stable (f : H₁ G →+ C) (t : I → C)
    (h : ∀ i x, f (map₁ (l i) x) = f (map₁ (r i) x)) (i : I) :
    P.lift₁ f t h (Additive.ofMul (Abelianization.of (P.stable i))) = t i := by
  simp [lift₁, P.lift_stable]

omit [DecidableEq I] in
theorem hom₁_ext (f g : H₁ K →+ C)
    (hbase : ∀ x, f (map₁ P.base x) = g (map₁ P.base x))
    (hstable : ∀ i, f (Additive.ofMul (Abelianization.of (P.stable i))) =
      g (Additive.ofMul (Abelianization.of (P.stable i)))) : f = g := by
  apply AddMonoidHom.toMultiplicativeRight.injective
  apply Abelianization.hom_ext
  apply P.hom_ext
  · intro a
    exact congrArg Multiplicative.ofAdd (hbase (Additive.ofMul (Abelianization.of a)))
  · intro i
    exact congrArg Multiplicative.ofAdd (hstable i)

/-- Exactness at the vertex abelianization, proved solely from the presentation. -/
theorem map₁_base_ker : (map₁ P.base).ker = (boundary₁ (l := l) (r := r)).range := by
  classical
  let E := boundary₁ (l := l) (r := r)
  let q := QuotientAddGroup.mk' E.range
  have hq : ∀ i x, q (map₁ (l i) x) = q (map₁ (r i) x) := by
    intro i x
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨DirectSum.of _ i x, boundary₁_of i x⟩
  apply le_antisymm
  · intro x hx
    have hh := P.lift₁_base q (fun _ ↦ 0) hq x
    change map₁ P.base x = 0 at hx
    rw [hx, map_zero] at hh
    exact (QuotientAddGroup.eq_zero_iff x).mp hh.symm
  · rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun P.map₁_base_boundary₁ x

/-- The vertex contribution to the abelianization. -/
abbrev VertexCokernel := H₁ G ⧸ (boundary₁ (l := l) (r := r)).range

noncomputable def vertexQuotient : H₁ G →+ VertexCokernel (l := l) (r := r) :=
  QuotientAddGroup.mk' _

theorem vertexQuotient_left_eq_right (i : I) (x : H₁ (A i)) :
    vertexQuotient (l := l) (r := r) (map₁ (l i) x) =
      vertexQuotient (l := l) (r := r) (map₁ (r i) x) := by
  classical
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨DirectSum.of _ i x, boundary₁_of i x⟩

noncomputable def vertexInclusion : VertexCokernel (l := l) (r := r) →+ H₁ K :=
  QuotientAddGroup.lift _ (map₁ P.base) (by rw [P.map₁_base_ker])

@[simp] theorem vertexInclusion_quotient (x : H₁ G) :
    P.vertexInclusion (vertexQuotient (l := l) (r := r) x) = map₁ P.base x := rfl

noncomputable def stableSection : FreeAbelianGroup I →+ H₁ K :=
  FreeAbelianGroup.lift fun i ↦ Additive.ofMul (Abelianization.of (P.stable i))

omit [DecidableEq I] in
@[simp] theorem stableSection_of (i : I) :
    P.stableSection (FreeAbelianGroup.of i) =
      Additive.ofMul (Abelianization.of (P.stable i)) := FreeAbelianGroup.lift_apply_of _ i

/-- Coordinates in the vertex cokernel and the free group of stable-letter exponents. -/
noncomputable def coordinates₁ :
    H₁ K →+ VertexCokernel (l := l) (r := r) × FreeAbelianGroup I :=
  P.lift₁ ((vertexQuotient (l := l) (r := r)).prod 0)
    (fun i ↦ (0, FreeAbelianGroup.of i)) (by
      intro i x
      exact Prod.ext (vertexQuotient_left_eq_right i x) rfl)

@[simp] theorem coordinates₁_base (x : H₁ G) :
    P.coordinates₁ (map₁ P.base x) = (vertexQuotient (l := l) (r := r) x, 0) :=
  P.lift₁_base _ _ _ x

@[simp] theorem coordinates₁_stable (i : I) :
    P.coordinates₁ (Additive.ofMul (Abelianization.of (P.stable i))) =
      (0, FreeAbelianGroup.of i) := P.lift₁_stable _ _ _ i

noncomputable def assemble₁ :
    VertexCokernel (l := l) (r := r) × FreeAbelianGroup I →+ H₁ K :=
  P.vertexInclusion.coprod P.stableSection

theorem assemble₁_coordinates₁ : P.assemble₁.comp P.coordinates₁ = AddMonoidHom.id _ := by
  apply P.hom₁_ext
  · intro x
    simp [assemble₁]
  · intro i
    simp [assemble₁]

theorem coordinates₁_vertexInclusion (x : VertexCokernel (l := l) (r := r)) :
    P.coordinates₁ (P.vertexInclusion x) = (x, 0) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  exact P.coordinates₁_base x

theorem coordinates₁_stableSection :
    P.coordinates₁.comp P.stableSection = AddMonoidHom.inr _ _ := by
  apply FreeAbelianGroup.lift_ext
  intro i
  simp

theorem coordinates₁_assemble₁ : P.coordinates₁.comp P.assemble₁ = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  rintro ⟨x, y⟩
  change P.coordinates₁ (P.vertexInclusion x + P.stableSection y) = (x,y)
  rw [map_add, P.coordinates₁_vertexInclusion]
  have hy := DFunLike.congr_fun P.coordinates₁_stableSection y
  change P.coordinates₁ (P.stableSection y) = (0,y) at hy
  rw [hy]
  simp

/-- The entire degree-one calculation for an arbitrary simultaneous HNN presentation. -/
noncomputable def abelianizationEquiv :
    H₁ K ≃+ VertexCokernel (l := l) (r := r) × FreeAbelianGroup I where
  toFun := P.coordinates₁
  invFun := P.assemble₁
  left_inv x := DFunLike.congr_fun P.assemble₁_coordinates₁ x
  right_inv x := DFunLike.congr_fun P.coordinates₁_assemble₁ x
  map_add' := map_add _

/-- Stable-letter exponent sums, split by the classes of the stable letters. -/
noncomputable def stableProjection : H₁ K →+ FreeAbelianGroup I :=
  (AddMonoidHom.snd _ _).comp P.coordinates₁

theorem stableProjection_section : P.stableProjection.comp P.stableSection = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  have h := DFunLike.congr_fun P.coordinates₁_stableSection x
  exact congrArg Prod.snd h

theorem stableProjection_surjective : Function.Surjective P.stableProjection := by
  intro x
  exact ⟨P.stableSection x, DFunLike.congr_fun P.stableProjection_section x⟩

/-- Exactness at the HNN abelianization; together with `map₁_base_ker` this is
the full degree-one tail of the graph-of-groups sequence. -/
theorem stableProjection_ker : P.stableProjection.ker = (map₁ P.base).range := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk'_surjective
      (boundary₁ (l := l) (r := r)).range (P.coordinates₁ x).1
    refine ⟨y, P.abelianizationEquiv.injective ?_⟩
    change P.coordinates₁ (map₁ P.base y) = P.coordinates₁ x
    rw [P.coordinates₁_base]
    exact Prod.ext hy hx.symm
  · rintro _ ⟨x, rfl⟩
    change (P.coordinates₁ (map₁ P.base x)).2 = 0
    rw [P.coordinates₁_base]

end HNNFamilyPresentation
end SmallPresentationStatements.Homology
