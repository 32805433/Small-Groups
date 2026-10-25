module

public import SmallPresentation.Homology

/-! Inner conjugation acts trivially on the canonical Hopf kernel. The proof
uses only the central relation extension, so it does not invoke a homology
comparison theorem, chain homotopy, or Mayer--Vietoris. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

variable (G : Type) [Group G]

/-- The canonical central relation extension, with codomain the original group. -/
def canonicalProjection : RelationExtension.Total (canonicalRelations G) →* G :=
  (QuotientGroup.kerLift (freeProjection G)).comp
    (RelationExtension.projection (canonicalRelations G))

@[simp] theorem canonicalProjection_mk (x : FreeGroup G) :
    canonicalProjection G
      (QuotientGroup.mk' (RelationExtension.commutatorKernel (canonicalRelations G)) x) =
        freeProjection G x := rfl

theorem canonicalProjection_central : UniversalCentralExtension.Central (canonicalProjection G) := by
  apply (UniversalCentralExtension.central_iff _).mpr
  intro x hx y
  apply RelationExtension.kernel_central (canonicalRelations G) x _ y
  apply QuotientGroup.kerLift_injective (freeProjection G)
  change canonicalProjection G x = 1 at hx
  simpa only [canonicalProjection, MonoidHom.comp_apply, map_one] using hx

variable {G} {H : Type} [Group H]

theorem canonicalProjection_totalMap (f : G →* H)
    (x : RelationExtension.Total (canonicalRelations G)) :
    canonicalProjection H
      (totalMap (canonicalRelations G) (canonicalRelations H)
        (FreeGroup.map f) (canonicalRelations_map f) x) = f (canonicalProjection G x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact DFunLike.congr_fun (freeProjection_map f) x

/-- Conjugate homomorphisms induce the same map on the Schur multiplier. -/
theorem schurMap_eq_of_conjugate (f g : G →* H) (c : H)
    (h : ∀ x, c * f x * c⁻¹ = g x) (x : Schur G) : schurMap f x = schurMap g x := by
  let N := canonicalRelations G
  let M := canonicalRelations H
  let F := totalMap N M (FreeGroup.map f) (canonicalRelations_map f)
  let T := totalMap N M (FreeGroup.map g) (canonicalRelations_map g)
  let z : RelationExtension.Total M := QuotientGroup.mk' (RelationExtension.commutatorKernel M)
    (FreeGroup.of c)
  have hz : canonicalProjection H z = c := by
    exact FreeGroup.lift_apply_of
  have heq : (canonicalProjection H).comp ((MulAut.conj z).toMonoidHom.comp F) =
      (canonicalProjection H).comp T := by
    apply MonoidHom.ext
    intro y
    change canonicalProjection H (z * F y * z⁻¹) = canonicalProjection H (T y)
    rw [map_mul, map_mul, map_inv, hz]
    rw [show canonicalProjection H (F y) = f (canonicalProjection G y) from
      canonicalProjection_totalMap f y]
    rw [show canonicalProjection H (T y) = g (canonicalProjection G y) from
      canonicalProjection_totalMap g y]
    exact h _
  have hagree := central_lifts_agree_on_commutator (canonicalProjection H)
    (canonicalProjection_central H) ((MulAut.conj z).toMonoidHom.comp F) T heq x.1.1 x.1.property
  have hFx : F x.1.1 ∈ (RelationExtension.projection M).ker := by
    change RelationExtension.projection M (F x.1.1) = 1
    rw [totalMap_projection]
    rw [show RelationExtension.projection N x.1.1 = 1 from x.property, map_one]
  have hc := RelationExtension.kernel_central M (F x.1.1) hFx z
  apply Subtype.ext
  apply Subtype.ext
  change F x.1.1 = T x.1.1
  change z * F x.1.1 * z⁻¹ = T x.1.1 at hagree
  simpa only [← hc, mul_assoc, mul_inv_cancel, mul_one] using hagree

/-- Inner automorphisms are invisible to integral degree-two homology. -/
theorem map₂_eq_of_conjugate (f g : G →* H) (c : H)
    (h : ∀ x, c * f x * c⁻¹ = g x) : map₂ f = map₂ g := by
  apply AddMonoidHom.ext
  intro x
  exact schurMap_eq_of_conjugate f g c h x.toMul

@[simp] theorem map₂_conj (c : G) : map₂ (MulAut.conj c).toMonoidHom = AddMonoidHom.id _ := by
  have h := map₂_eq_of_conjugate (MonoidHom.id G) (MulAut.conj c).toMonoidHom c (fun _ ↦ rfl)
  rw [← h]
  apply AddMonoidHom.ext
  intro x
  exact schurMap_id x.toMul

end SmallPresentationStatements.Homology
