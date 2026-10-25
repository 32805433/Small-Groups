module

public import SmallPresentation.RelationCoordinates

/-! The quotient action on the abelianization of a normal subgroup. -/
@[expose] public section

namespace SmallPresentationStatements.RelationAbelianization

open RelationCoordinates

variable {F : Type} [Group F] (N : Subgroup F) [N.Normal]

/-- The additive underlying group of the relation module. -/
abbrev Module := Additive (Abelianization N)

/-- The class of a relation in its abelianization. -/
def of : N →* Multiplicative (Module N) := Abelianization.of

/-- Ambient conjugation on the relation abelianization. -/
def conjugationMap (f : F) : Module N →+ Module N :=
  (Abelianization.map (conjugation N f)).toAdditive

@[simp] theorem conjugationMap_of (f : F) (n : N) :
    conjugationMap N f (Additive.ofMul (Abelianization.of n)) =
      Additive.ofMul (Abelianization.of (conjugation N f n)) := rfl

/-- Equal quotient representatives induce the same map on the relation module. -/
theorem conjugationMap_eq (f g : F)
    (h : QuotientGroup.mk' N f = QuotientGroup.mk' N g) :
    conjugationMap N f = conjugationMap N g := by
  have hv : f * g⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (f * g⁻¹) = 1
    simp only [map_mul, map_inv, h, mul_inv_cancel]
  let v : N := ⟨f * g⁻¹, hv⟩
  have heq (n : N) : conjugation N f n = v * conjugation N g n * v⁻¹ := by
    apply Subtype.ext
    change f * n.val * f⁻¹ =
      (f * g⁻¹) * (g * n.val * g⁻¹) * (f * g⁻¹)⁻¹
    group
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x.toMul
  change Additive.ofMul (Abelianization.of (conjugation N f n)) =
    Additive.ofMul (Abelianization.of (conjugation N g n))
  rw [heq]
  simp

/-- A representative of a quotient element; only its quotient law is used. -/
noncomputable def representative (q : F ⧸ N) : F :=
  Classical.choose (QuotientGroup.mk'_surjective N q)

@[simp] theorem representative_spec (q : F ⧸ N) :
    QuotientGroup.mk' N (representative N q) = q :=
  Classical.choose_spec (QuotientGroup.mk'_surjective N q)

/-- Quotient conjugation, independent of the chosen representative. -/
noncomputable def quotientAction (q : F ⧸ N) : Module N →+ Module N :=
  conjugationMap N (representative N q)

@[simp] theorem quotientAction_mk (f : F) :
    quotientAction N (QuotientGroup.mk' N f) = conjugationMap N f :=
  conjugationMap_eq N _ _ (representative_spec N _)

@[simp] theorem conjugationMap_one : conjugationMap N 1 = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x.toMul
  change Additive.ofMul (Abelianization.of (conjugation N 1 n)) =
    Additive.ofMul (Abelianization.of n)
  congr 2
  apply Subtype.ext
  simp [conjugation]

@[simp] theorem conjugationMap_mul (f g : F) :
    conjugationMap N (f * g) = (conjugationMap N f).comp (conjugationMap N g) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x.toMul
  change Additive.ofMul (Abelianization.of (conjugation N (f * g) n)) =
    Additive.ofMul (Abelianization.of (conjugation N f (conjugation N g n)))
  congr 2
  apply Subtype.ext
  simp [conjugation, mul_assoc]

@[simp] theorem quotientAction_one : quotientAction N 1 = AddMonoidHom.id _ := by
  have h := quotientAction_mk N (1 : F)
  simpa using h

@[simp] theorem quotientAction_mul (q r : F ⧸ N) :
    quotientAction N (q * r) = (quotientAction N q).comp (quotientAction N r) := by
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N r
  rw [← map_mul, quotientAction_mk, quotientAction_mk, quotientAction_mk,
    conjugationMap_mul]

end SmallPresentationStatements.RelationAbelianization
