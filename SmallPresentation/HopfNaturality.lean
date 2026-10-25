module

public import SmallPresentation.Homology

/-! Natural comparison of arbitrary free presentations with the canonical Hopf model. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable {X Y Z : Type}
variable (N : Subgroup (FreeGroup X)) (M : Subgroup (FreeGroup Y))
    (K : Subgroup (FreeGroup Z)) [N.Normal] [M.Normal] [K.Normal]

theorem presentationMap_id (x : PresentationKernel N) :
    presentationMap N N (MonoidHom.id _) le_rfl x = x := by
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel N) x.val.val
  change totalMap N N (MonoidHom.id _) le_rfl x.val.val = x.val.val
  rw [← hy]
  rfl

theorem presentationMap_comp (f : FreeGroup X →* FreeGroup Y)
    (g : FreeGroup Y →* FreeGroup Z) (hf : N ≤ M.comap f) (hg : M ≤ K.comap g)
    (x : PresentationKernel N) :
    presentationMap M K g hg (presentationMap N M f hf x) =
      presentationMap N K (g.comp f) (fun _ hx ↦ hg (hf hx)) x := by
  apply Subtype.ext
  apply Subtype.ext
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel N) x.val.val
  change totalMap M K g hg (totalMap N M f hf x.val.val) =
    totalMap N K (g.comp f) (fun _ hx ↦ hg (hf hx)) x.val.val
  rw [← hy]
  rfl

/-- Free lifts inducing the same quotient homomorphism induce the same Hopf map. -/
theorem presentationMap_ext (f g : FreeGroup X →* FreeGroup Y)
    (hf : N ≤ M.comap f) (hg : N ≤ M.comap g)
    (h : (QuotientGroup.mk' M).comp f = (QuotientGroup.mk' M).comp g)
    (x : PresentationKernel N) :
    presentationMap N M f hf x = presentationMap N M g hg x := by
  apply Subtype.ext
  apply Subtype.ext
  apply central_lifts_agree_on_commutator (RelationExtension.projection M)
    ((UniversalCentralExtension.central_iff _).mpr (RelationExtension.kernel_central M))
    (totalMap N M f hf) (totalMap N M g hg)
  · apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (RelationExtension.commutatorKernel N) y
    exact DFunLike.congr_fun h z
  · exact x.val.property

variable {B C : Type} [Group B] [Group C]

/-- Evaluation into the canonical free group on the underlying group elements. -/
def presentationComparison (p : FreeGroup X →* B) : FreeGroup X →* FreeGroup B :=
  FreeGroup.lift (fun x ↦ FreeGroup.of (p (FreeGroup.of x)))

theorem presentationComparison_spec (p : FreeGroup X →* B) :
    (freeProjection B).comp (presentationComparison p) = p := by
  apply FreeGroup.ext_hom
  intro x
  simp [presentationComparison, freeProjection]

theorem presentationComparison_relations (p : FreeGroup X →* B) :
    p.ker ≤ (canonicalRelations B).comap (presentationComparison p) := by
  intro x hx
  change freeProjection B (presentationComparison p x) = 1
  rw [← MonoidHom.comp_apply, presentationComparison_spec]
  exact hx

noncomputable def presentationInverse (p : FreeGroup X →* B)
    (hp : Function.Surjective p) : FreeGroup B →* FreeGroup X :=
  FreeGroup.lift (fun b ↦ Classical.choose (hp b))

theorem presentationInverse_spec (p : FreeGroup X →* B) (hp : Function.Surjective p) :
    p.comp (presentationInverse p hp) = freeProjection B := by
  apply FreeGroup.ext_hom
  intro b
  change p (FreeGroup.lift _ (FreeGroup.of b)) = freeProjection B (FreeGroup.of b)
  rw [FreeGroup.lift_apply_of]
  simpa [freeProjection] using Classical.choose_spec (hp b)

theorem presentationInverse_relations (p : FreeGroup X →* B) (hp : Function.Surjective p) :
    canonicalRelations B ≤ p.ker.comap (presentationInverse p hp) := by
  intro x hx
  change p (presentationInverse p hp x) = 1
  rw [← MonoidHom.comp_apply, presentationInverse_spec]
  exact hx

theorem quotientKer_comp_eq (p : FreeGroup Y →* B) (hp : Function.Surjective p)
    (f g : FreeGroup X →* FreeGroup Y) (h : p.comp f = p.comp g) :
    (QuotientGroup.mk' p.ker).comp f = (QuotientGroup.mk' p.ker).comp g := by
  apply MonoidHom.ext
  intro x
  apply (QuotientGroup.quotientKerEquivOfSurjective p hp).injective
  exact DFunLike.congr_fun h x

/-- A specified natural comparison, rather than an unspecified existence of an isomorphism. -/
noncomputable def hopfEquivOfPresentation (p : FreeGroup X →* B)
    (hp : Function.Surjective p) : PresentationKernel p.ker ≃* Schur B where
  toFun := presentationMap p.ker (canonicalRelations B) (presentationComparison p)
    (presentationComparison_relations p)
  invFun := presentationMap (canonicalRelations B) p.ker (presentationInverse p hp)
    (presentationInverse_relations p hp)
  left_inv x := by
    rw [presentationMap_comp]
    calc
      _ = presentationMap p.ker p.ker (MonoidHom.id _) le_rfl x := by
        apply presentationMap_ext
        apply quotientKer_comp_eq p hp
        rw [← MonoidHom.comp_assoc, presentationInverse_spec, presentationComparison_spec]
        rfl
      _ = x := presentationMap_id _ x
  right_inv x := by
    rw [presentationMap_comp]
    calc
      _ = presentationMap (canonicalRelations B) (canonicalRelations B)
          (MonoidHom.id _) le_rfl x := by
        apply presentationMap_ext
        apply quotientKer_comp_eq (freeProjection B)
          (fun b ↦ ⟨FreeGroup.of b, FreeGroup.lift_apply_of⟩)
        rw [← MonoidHom.comp_assoc, presentationComparison_spec, presentationInverse_spec]
        rfl
      _ = x := presentationMap_id _ x
  map_mul' := map_mul _

/-- Naturality with respect to the actual group homomorphism represented by a free lift. -/
theorem hopfEquivOfPresentation_natural (p : FreeGroup X →* B)
    (q : FreeGroup Y →* C) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (f : FreeGroup X →* FreeGroup Y) (g : B →* C) (h : q.comp f = g.comp p)
    (hf : p.ker ≤ q.ker.comap f) (x : PresentationKernel p.ker) :
    hopfEquivOfPresentation q hq (presentationMap p.ker q.ker f hf x) =
      schurMap g (hopfEquivOfPresentation p hp x) := by
  change presentationMap _ _ _ _ (presentationMap _ _ _ _ x) =
    presentationMap _ _ _ _ (presentationMap _ _ _ _ x)
  rw [presentationMap_comp, presentationMap_comp]
  apply presentationMap_ext
  apply quotientKer_comp_eq (freeProjection C)
    (fun c ↦ ⟨FreeGroup.of c, FreeGroup.lift_apply_of⟩)
  rw [← MonoidHom.comp_assoc, presentationComparison_spec,
    ← MonoidHom.comp_assoc, freeProjection_map, MonoidHom.comp_assoc,
    presentationComparison_spec]
  exact h

theorem hopfEquivOfPresentation_canonical
    (hp : Function.Surjective (freeProjection B)) (x : Schur B) :
    hopfEquivOfPresentation (freeProjection B) hp x = x := by
  change presentationMap _ _ _ _ x = x
  calc
    _ = presentationMap (canonicalRelations B) (canonicalRelations B)
        (MonoidHom.id _) le_rfl x := by
      apply presentationMap_ext
      apply quotientKer_comp_eq (freeProjection B) hp
      rw [presentationComparison_spec]
      rfl
    _ = x := presentationMap_id _ x

/-- The comparison with an explicitly named presentation kernel. -/
noncomputable def hopfEquivWithKernel (N : Subgroup (FreeGroup X)) [N.Normal]
    (p : FreeGroup X →* B) (hp : Function.Surjective p) (hk : p.ker = N) :
    PresentationKernel N ≃* Schur B := by
  subst N
  exact hopfEquivOfPresentation p hp

theorem hopfEquivWithKernel_natural
    (N : Subgroup (FreeGroup X)) (M : Subgroup (FreeGroup Y)) [N.Normal] [M.Normal]
    (p : FreeGroup X →* B) (q : FreeGroup Y →* C)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpk : p.ker = N) (hqk : q.ker = M)
    (f : FreeGroup X →* FreeGroup Y) (g : B →* C) (h : q.comp f = g.comp p)
    (hf : N ≤ M.comap f) (x : PresentationKernel N) :
    hopfEquivWithKernel M q hq hqk (presentationMap N M f hf x) =
      schurMap g (hopfEquivWithKernel N p hp hpk x) := by
  subst N
  subst M
  exact hopfEquivOfPresentation_natural p q hp hq f g h hf x

@[simp] theorem hopfEquivWithKernel_canonical
    (hp : Function.Surjective (freeProjection B)) (x : Schur B) :
    hopfEquivWithKernel (canonicalRelations B) (freeProjection B) hp rfl x = x :=
  hopfEquivOfPresentation_canonical hp x

end SmallPresentationStatements.Homology
