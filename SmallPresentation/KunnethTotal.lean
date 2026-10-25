module

public import SmallPresentation.KunnethCommutator
public import SmallPresentation.KunnethSplitting

/-! Canonical central extensions and their universal lifting property. These
lemmas expose the concrete Hopf model without choosing a presentation of a
direct product. -/
@[expose] public section

namespace SmallPresentationStatements.Homology

open scoped commutatorElement

variable (G : Type) [Group G]

abbrev CanonicalTotal := RelationExtension.Total (canonicalRelations G)

def totalGenerator (g : G) : CanonicalTotal G :=
  QuotientGroup.mk' _ (FreeGroup.of g)

def totalEvaluation : CanonicalTotal G →* G :=
  QuotientGroup.lift _ (freeProjection G) (Subgroup.commutator_le_left _ _)

@[simp] theorem totalEvaluation_mk (w : FreeGroup G) :
    totalEvaluation G (QuotientGroup.mk' _ w) = freeProjection G w := rfl

@[simp] theorem totalEvaluation_generator (g : G) :
    totalEvaluation G (totalGenerator G g) = g := FreeGroup.lift_apply_of

theorem totalEvaluation_surjective : Function.Surjective (totalEvaluation G) :=
  fun g ↦ ⟨totalGenerator G g,totalEvaluation_generator G g⟩

theorem totalEvaluation_eq_one_iff (x : CanonicalTotal G) :
    totalEvaluation G x = 1 ↔ RelationExtension.projection (canonicalRelations G) x = 1 := by
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact (QuotientGroup.eq_one_iff (N := canonicalRelations G) w).symm

theorem totalEvaluation_central : UniversalCentralExtension.Central (totalEvaluation G) := by
  apply (UniversalCentralExtension.central_iff _).mpr
  intro z hz x
  exact RelationExtension.kernel_central (canonicalRelations G) z
    ((totalEvaluation_eq_one_iff G z).mp hz) x

def centralDerivedKernelEquiv :
    CentralDerivedKernel (totalEvaluation G) (totalEvaluation_central G) ≃* Schur G where
  toFun x := ⟨x.1,(totalEvaluation_eq_one_iff G x.1.1).mp x.2⟩
  invFun x := ⟨x.1,(totalEvaluation_eq_one_iff G x.1.1).mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {G} {E : Type} [Group E]

def canonicalTotalLift (π : E →* G) (hc : UniversalCentralExtension.Central π)
    (s : G → E) (hs : ∀ g, π (s g) = g) : CanonicalTotal G →* E :=
  QuotientGroup.lift _ (FreeGroup.lift s) (by
    apply Subgroup.commutator_le.mpr
    intro n hn w _
    change FreeGroup.lift s ⁅n,w⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply (UniversalCentralExtension.central_iff π).mp hc
    change π (FreeGroup.lift s n) = 1
    have heq : π.comp (FreeGroup.lift s) = freeProjection G := by
      apply FreeGroup.ext_hom
      intro g
      simpa [freeProjection] using hs g
    rw [← MonoidHom.comp_apply, heq]
    exact hn)

@[simp] theorem canonicalTotalLift_generator (π : E →* G)
    (hc : UniversalCentralExtension.Central π) (s : G → E) (hs : ∀ g, π (s g) = g)
    (g : G) : canonicalTotalLift π hc s hs (totalGenerator G g) = s g :=
  FreeGroup.lift_apply_of

theorem canonicalTotalLift_projection (π : E →* G)
    (hc : UniversalCentralExtension.Central π) (s : G → E) (hs : ∀ g, π (s g) = g) :
    π.comp (canonicalTotalLift π hc s hs) = totalEvaluation G := by
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective _ x
  change π (FreeGroup.lift s w) = freeProjection G w
  have heq : π.comp (FreeGroup.lift s) = freeProjection G := by
    apply FreeGroup.ext_hom
    intro g
    simpa [freeProjection] using hs g
  exact DFunLike.congr_fun heq w

variable {H : Type} [Group H]

def canonicalTotalMap (f : G →* H) : CanonicalTotal G →* CanonicalTotal H :=
  totalMap (canonicalRelations G) (canonicalRelations H) (FreeGroup.map f)
    (canonicalRelations_map f)

@[simp] theorem canonicalTotalMap_generator (f : G →* H) (g : G) :
    canonicalTotalMap f (totalGenerator G g) = totalGenerator H (f g) := by
  simp [canonicalTotalMap, totalGenerator, totalMap]

theorem canonicalTotalMap_projection (f : G →* H) (x : CanonicalTotal G) :
    totalEvaluation H (canonicalTotalMap f x) = f (totalEvaluation G x) := by
  obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective _ x
  exact DFunLike.congr_fun (freeProjection_map f) w

theorem canonicalTotalMap_schur (f : G →* H) (x : Schur G) :
    (schurMap f x).1.1 = canonicalTotalMap f x.1.1 := rfl

end SmallPresentationStatements.Homology
