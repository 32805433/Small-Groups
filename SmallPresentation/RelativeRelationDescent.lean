module

public import SmallPresentation.QuotientRelatorLifts
public import SmallPresentation.RelativeIdentityDescent
public import SmallPresentation.WeightedNaturality

/-!
# The relation-module basis after imposing the old relations

The relative weighted identity condition on a lifted presentation descends to the
actual base quotient. Its conjugated new relators form a basis of the full relation
abelianization, not just of the central coinvariants. No freeness or finiteness
assumptions on the ambient groups are needed.
-/
@[expose] public section

namespace SmallPresentationStatements.QuotientRelatorLifts

open RelationCoordinates

variable {E F O I : Type} [Group E] [Group F]
    (p : E →* F) (hp : Function.Surjective p) (old : O → E)
    (hker : p.ker = Relations old) (new : I → E)

include hp hker in
/-- Quotient-weighted old/new identities descend to quotient-weighted new identities. -/
theorem weighted_descends
    (h : Weighted.Balanced (Sum.elim old new)
      (QuotientGroup.mk' (liftedRelations old new)) RelativeWeighted.newLabel) :
    Weighted.Balanced (fun i ↦ p (new i))
      (QuotientGroup.mk' (targetRelations p new)) (some : I → Option I) := by
  have ht := Weighted.balanced_map (Sum.elim old new)
    (QuotientGroup.mk' (liftedRelations old new)) (fromLifted p old hker new)
    RelativeWeighted.newLabel h
  have he : (fromLifted p old hker new).comp
      (QuotientGroup.mk' (liftedRelations old new)) =
      (QuotientGroup.mk' (targetRelations p new)).comp p := by
    ext x
    rfl
  rw [he] at ht
  exact RelativeIdentity.weighted_balanced_descends old new p hp hker
    (QuotientGroup.mk' (targetRelations p new)) ht

/-- The actual conjugates of the new relators give the descended relation-module basis. -/
noncomputable def relationBasis
    (h : Weighted.Balanced (Sum.elim old new)
      (QuotientGroup.mk' (liftedRelations old new)) RelativeWeighted.newLabel) :
    FreeAbelianGroup (Target p new × I) ≃+
      RelationAbelianization.Module (targetRelations p new) :=
  WeightedBasis.equiv (fun i ↦ p (new i)) (weighted_descends p hp old hker new h)

@[simp] theorem relationBasis_of
    (h : Weighted.Balanced (Sum.elim old new)
      (QuotientGroup.mk' (liftedRelations old new)) RelativeWeighted.newLabel)
    (f : F) (i : I) :
    relationBasis p hp old hker new h
      (FreeAbelianGroup.of (QuotientGroup.mk' (targetRelations p new) f, i)) =
      WeightedBasis.conjugateClass (fun i ↦ p (new i)) f i :=
  WeightedBasis.equiv_of _ _ _ _

include hp hker in
/-- In particular, the scalar identities used by the existing theorem assembly are balanced. -/
theorem scalar_descends
    (h : Weighted.Balanced (Sum.elim old new)
      (QuotientGroup.mk' (liftedRelations old new)) RelativeWeighted.newLabel) :
    IdentitySequencesBalanced (fun i ↦ p (new i)) :=
  Weighted.balanced_of_all_labelled _ _ (weighted_descends p hp old hker new h)

end SmallPresentationStatements.QuotientRelatorLifts
