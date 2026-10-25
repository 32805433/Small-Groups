module

public import SmallPresentation.CyclicModulePresentation
public import SmallPresentation.RelationAbelianization

/-! Identification of the two canonical constructions of the relation module:
the kernel of the quotient presentation and the specified normal subgroup. This
identification respects the actual quotient action and its periodic complex. -/
@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open RelationDerivative

variable {X : Type} (N : Subgroup (FreeGroup X)) [N.Normal]

/-- Identify the kernel of the quotient map with its specified normal subgroup. -/
def quotientRelationEquiv :
    Additive (Abelianization (QuotientGroup.mk' N).ker) ≃+
      RelationAbelianization.Module N :=
  (MulEquiv.abelianizationCongr
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N))).toAdditive

/-- The identification respects quotient conjugation, independently of the two choices
of representatives used to define the actions. -/
theorem quotientRelationEquiv_action (c : FreeGroup X ⧸ N)
    (a : Additive (Abelianization (QuotientGroup.mk' N).ker)) :
    quotientRelationEquiv N
      (presentationAction (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c a) =
    RelationAbelianization.quotientAction N c (quotientRelationEquiv N a) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective N c
  change quotientRelationEquiv N
    (relationShift (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
      (QuotientGroup.mk' N w) a) = _
  rw [relationShift_eq_conjugation, RelationAbelianization.quotientAction_mk]
  induction a using QuotientGroup.induction_on with
  | H r =>
    change Additive.ofMul (Abelianization.of _) = Additive.ofMul (Abelianization.of _)
    congr 2

/-- The actual quotient action, packaged as an additive endomorphism. -/
noncomputable def quotientRelationAction (c : FreeGroup X ⧸ N) :
    AddMonoid.End (RelationAbelianization.Module N) :=
  RelationAbelianization.quotientAction N c

theorem quotientRelationAction_pow_order (c : FreeGroup X ⧸ N) :
    quotientRelationAction N c ^ orderOf c = 1 := by
  apply AddMonoid.End.ext
  intro b
  obtain ⟨a, rfl⟩ := (quotientRelationEquiv N).surjective b
  calc
    _ = quotientRelationEquiv N
        ((presentationAction (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c ^
          orderOf c) a) :=
      (commute_powers
        (presentationAction (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c)
        (quotientRelationAction N c) (quotientRelationEquiv N).toAddMonoidHom
        (quotientRelationEquiv_action N c) (orderOf c) a).symm
    _ = _ := by rw [presentationAction_pow_order]; rfl

/-- The canonical relation-module equivalence intertwines norm and difference. -/
theorem quotientRelationEquiv_compatible (c : FreeGroup X ⧸ N)
    (ht : quotientRelationAction N c ^ orderOf c = 1) :
    Periodic.Compatible
      (presentationPeriodic (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c)
      (ofFiniteOrder (quotientRelationAction N c) (orderOf c) ht)
      (quotientRelationEquiv N).toAddMonoidHom :=
  ofFiniteOrder_compatible _ _ _ _ _ _ (quotientRelationEquiv_action N c)

/-- Even exactness is invariant under the canonical identification of relation modules. -/
theorem presentation_evenExact_iff_quotientAction (c : FreeGroup X ⧸ N)
    (ht : quotientRelationAction N c ^ orderOf c = 1) :
    (presentationPeriodic (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c).EvenExact ↔
      (ofFiniteOrder (quotientRelationAction N c) (orderOf c) ht).EvenExact := by
  constructor
  · exact Periodic.evenExact_of_equiv _ _ (quotientRelationEquiv N)
      (quotientRelationEquiv_compatible N c ht)
  · exact Periodic.evenExact_of_equiv _ _ (quotientRelationEquiv N).symm
      ((quotientRelationEquiv_compatible N c ht).equiv_symm)

/-- Transport actual quotient-action exactness into the presentation torsion criterion. -/
theorem presentation_evenExact_of_quotientAction (c : FreeGroup X ⧸ N)
    (ht : quotientRelationAction N c ^ orderOf c = 1)
    (he : (ofFiniteOrder (quotientRelationAction N c) (orderOf c) ht).EvenExact) :
    (presentationPeriodic (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) c).EvenExact :=
  (presentation_evenExact_iff_quotientAction N c ht).mpr he

/-- The group-level obstruction can be stated entirely with the normal subgroup's
canonical quotient action. -/
theorem torsionFree_quotient_of_relation_evenExact
    (he : ∀ c : FreeGroup X ⧸ N, IsOfFinOrder c →
      (ofFiniteOrder (quotientRelationAction N c) (orderOf c)
        (quotientRelationAction_pow_order N c)).EvenExact) :
    IsMulTorsionFree (FreeGroup X ⧸ N) := by
  apply torsionFree_of_presentation_evenExact (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)
  intro c hc
  exact presentation_evenExact_of_quotientAction N c
    (quotientRelationAction_pow_order N c) (he c hc)

end SmallPresentationStatements.CyclicModule
