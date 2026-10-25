module

public import SmallPresentation.RelationDerivativeNaturality
public import Mathlib.Algebra.DirectSum.Basic

/-! Independence of translated factor relation modules detected by disjoint Cayley
edge alphabets. The indexing may include arbitrary chosen factor-coset representatives. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative

open DirectSum
attribute [local instance] Classical.propDecidable

variable {ι : Type} (B : ι → Type)

/-- Assemble free abelian groups on separate alphabets into their tagged alphabet. -/
noncomputable def sumFreeAbelian :
    (⨁ i, FreeAbelianGroup (B i)) →+ FreeAbelianGroup (Σ i, B i) :=
  DirectSum.toAddMonoid (fun i ↦ FreeAbelianGroup.map (Sigma.mk i))

/-- Separate the tagged free abelian alphabet into its direct summands. -/
noncomputable def splitFreeAbelian :
    FreeAbelianGroup (Σ i, B i) →+ (⨁ i, FreeAbelianGroup (B i)) :=
  FreeAbelianGroup.lift (fun b ↦ DirectSum.of (fun i ↦ FreeAbelianGroup (B i)) b.1
    (FreeAbelianGroup.of b.2))

@[simp] theorem sumFreeAbelian_of (i : ι) (c : FreeAbelianGroup (B i)) :
    sumFreeAbelian B (DirectSum.of _ i c) = FreeAbelianGroup.map (Sigma.mk i) c :=
  DirectSum.toAddMonoid_of _ _ _

@[simp] theorem splitFreeAbelian_of (i : ι) (b : B i) :
    splitFreeAbelian B (FreeAbelianGroup.of ⟨i, b⟩) =
      DirectSum.of _ i (FreeAbelianGroup.of b) := by
  simp [splitFreeAbelian]

theorem split_sumFreeAbelian (c : ⨁ i, FreeAbelianGroup (B i)) :
    splitFreeAbelian B (sumFreeAbelian B c) = c := by
  have he : (splitFreeAbelian B).comp (sumFreeAbelian B) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext'
    intro i
    apply FreeAbelianGroup.lift_ext
    intro b
    simp
  exact DFunLike.congr_fun he c

theorem sumFreeAbelian_injective : Function.Injective (sumFreeAbelian B) :=
  Function.LeftInverse.injective (split_sumFreeAbelian B)

variable {C : Type} (f : (Σ i, B i) → C)

/-- The simultaneous map of all the separate free abelian alphabets. -/
noncomputable def sumFreeMap : (⨁ i, FreeAbelianGroup (B i)) →+ FreeAbelianGroup C :=
  (FreeAbelianGroup.map f).comp (sumFreeAbelian B)

@[simp] theorem sumFreeMap_of (i : ι) (c : FreeAbelianGroup (B i)) :
    sumFreeMap B f (DirectSum.of _ i c) = FreeAbelianGroup.map (fun b ↦ f ⟨i, b⟩) c := by
  simp only [sumFreeMap, AddMonoidHom.comp_apply, sumFreeAbelian_of]
  exact (FreeAbelianGroup.map_comp_apply c).symm

theorem sumFreeMap_injective (hf : Function.Injective f) :
    Function.Injective (sumFreeMap B f) :=
  (freeAbelian_map_injective f hf).comp (sumFreeAbelian_injective B)

section Relations

variable {Y Q : Type} [Group Q]
  (X : ι → Type) (G : ι → Type) [∀ i, Group (G i)]
  (p : ∀ i, FreeGroup (X i) →* G i) (q : FreeGroup Y →* Q)
  (letters : ∀ i, X i → Y) (φ : ∀ i, G i →* Q)
  (compat : ∀ i, q.comp (FreeGroup.map (letters i)) = (φ i).comp (p i))
  (conjugator : ι → FreeGroup Y)

/-- The edge alphabet of all translated factors. -/
def translatedEdge (e : Σ i, G i × X i) : Q × Y :=
  (q (conjugator e.1) * φ e.1 e.2.1, letters e.1 e.2.2)

/-- Include a factor relation module and translate by its chosen representative. -/
def translatedRelationMap (i : ι) :
    Additive (Abelianization (p i).ker) →+ Additive (Abelianization q.ker) :=
  (relationConjugation q (conjugator i)).comp
    (relationMap (p i) q (letters i) (φ i) (compat i))

/-- Assemble the translated old factor relation modules. -/
noncomputable def translatedRelationSum :
    (⨁ i, Additive (Abelianization (p i).ker)) →+ Additive (Abelianization q.ker) :=
  DirectSum.toAddMonoid (translatedRelationMap X G p q letters φ compat conjugator)

@[simp] theorem translatedRelationSum_of (i : ι)
    (c : Additive (Abelianization (p i).ker)) :
    translatedRelationSum X G p q letters φ compat conjugator (DirectSum.of _ i c) =
      translatedRelationMap X G p q letters φ compat conjugator i c :=
  DirectSum.toAddMonoid_of _ _ _

theorem derivative_translatedRelationMap (i : ι)
    (c : Additive (Abelianization (p i).ker)) :
    relationDerivative q (translatedRelationMap X G p q letters φ compat conjugator i c) =
      FreeAbelianGroup.map (fun e : G i × X i ↦
        translatedEdge X G q letters φ conjugator ⟨i, e⟩) (relationDerivative (p i) c) := by
  rw [translatedRelationMap, AddMonoidHom.comp_apply, relationDerivative_conjugation,
    relationDerivative_natural]
  have he : (shift (q (conjugator i))).comp (chainMap (letters i) (φ i)) =
      FreeAbelianGroup.map (fun e : G i × X i ↦
        translatedEdge X G q letters φ conjugator ⟨i, e⟩) := by
    apply FreeAbelianGroup.lift_ext
    rintro ⟨g, x⟩
    rfl
  exact DFunLike.congr_fun he _

theorem derivative_translatedRelationSum
    (c : ⨁ i, Additive (Abelianization (p i).ker)) :
    relationDerivative q (translatedRelationSum X G p q letters φ compat conjugator c) =
      sumFreeMap (fun i ↦ G i × X i) (translatedEdge X G q letters φ conjugator)
        (DirectSum.map (fun i ↦ relationDerivative (p i)) c) := by
  have he : (relationDerivative q).comp
      (translatedRelationSum X G p q letters φ compat conjugator) =
      (sumFreeMap (fun i ↦ G i × X i) (translatedEdge X G q letters φ conjugator)).comp
        (DirectSum.map (fun i ↦ relationDerivative (p i))) := by
    apply DirectSum.addHom_ext
    intro i z
    simp only [AddMonoidHom.comp_apply, translatedRelationSum_of, DirectSum.map_of,
      sumFreeMap_of]
    exact derivative_translatedRelationMap X G p q letters φ compat conjugator i z
  exact DFunLike.congr_fun he c

/-- Disjoint translated edge alphabets make all factor relation modules independent. -/
theorem translatedRelationSum_injective (hp : ∀ i, Function.Surjective (p i))
    (hedges : Function.Injective (translatedEdge X G q letters φ conjugator)) :
    Function.Injective (translatedRelationSum X G p q letters φ compat conjugator) := by
  intro c d he
  have hm : Function.Injective (DirectSum.map (fun i ↦ relationDerivative (p i))) :=
    (DirectSum.map_injective (fun i ↦ relationDerivative (p i))).mpr
      (fun i ↦ relationDerivative_injective (p i) (hp i))
  apply hm
  apply sumFreeMap_injective (fun i ↦ G i × X i)
    (translatedEdge X G q letters φ conjugator) hedges
  rw [← derivative_translatedRelationSum X G p q letters φ compat conjugator,
    ← derivative_translatedRelationSum X G p q letters φ compat conjugator, he]

end Relations

end SmallPresentationStatements.RelationDerivative
