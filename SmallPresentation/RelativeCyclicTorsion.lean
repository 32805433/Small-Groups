module

public import SmallPresentation.RelationDerivativeCyclicOldTorsion
public import SmallPresentation.CyclicModuleExactSequence
public import SmallPresentation.RelationPeriodic

/-! Combine the old and new relation modules through their actual equivariant
short exact sequence. The free new coordinates have regular cyclic action. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

open RelationCoordinates CyclicModule

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a) (new : I → FreeGroup (Σ a, X a))

/-- The old-image action has every period of the ambient quotient element. -/
theorem oldAction_period_of_pow (q : Quotient X G p new) (n : ℕ) (hq : q ^ n = 1) :
    oldAction X G p new q ^ n = 1 := by
  apply AddMonoid.End.ext
  intro z
  apply Subtype.ext
  have hc := commute_powers (oldAction X G p new q)
    (quotientRelationAction (Relations X G p new) q)
    (RelativeWeighted.oldMap (old X G p) new).range.subtype (fun _ ↦ rfl) n z
  rw [RelationAbelianization.quotientAction_period _ _ _ hq] at hc
  exact hc

/-- The old-image periodic complex, with its actual quotient action. -/
noncomputable def oldPeriodic (q : Quotient X G p new) (n : ℕ) (hq : q ^ n = 1) :
    Periodic (RelativeWeighted.oldMap (old X G p) new).range :=
  ofFiniteOrder (oldAction X G p new q) n (oldAction_period_of_pow X G p new q n hq)

/-- Even exactness of the old summand implies even exactness of the full relation
module. The argument uses the weighted projection and does not assume a split
sequence of group-ring modules. -/
theorem relation_evenExact_of_old
    (hbalanced : Weighted.Balanced (all X G p new) (quotient X G p new)
      RelativeWeighted.newLabel)
    (q : Quotient X G p new) (hq : IsOfFinOrder q) (n : ℕ) (hn : orderOf q = n + 1)
    (hOld : (oldPeriodic X G p new q (n + 1) (by rw [← hn]; exact pow_orderOf_eq_one _)).EvenExact) :
    (RelationAbelianization.periodic (Relations X G p new) q (n + 1)
      (by rw [← hn]; exact pow_orderOf_eq_one _)).EvenExact := by
  let P := RelativeWeighted.projection (old X G p) new hbalanced
  let inc := (RelativeWeighted.oldMap (old X G p) new).range.subtype
  let tNew := permutationAction (labelledTranslation I q)
  have hNew : tNew ^ (n + 1) = 1 := permutation_pow_order n
    (labelledOrbitCoordinates I q hq n hn) (labelledTranslation I q)
    (labelledOrbitCoordinates_step I q hq n hn)
  apply Periodic.evenExact_of_exact_three_term
    (oldPeriodic X G p new q (n + 1) _) _ (ofFiniteOrder tNew (n + 1) hNew)
    inc P Subtype.val_injective
  · rw [RelativeWeighted.projection_ker]
    exact AddSubgroup.range_subtype _ |>.symm
  · intro v
    exact ⟨RelativeWeighted.newMap (old X G p) new v,
      DFunLike.congr_fun (RelativeWeighted.projection_newMap (old X G p) new hbalanced) v⟩
  · apply ofFiniteOrder_compatible
    intro z
    rfl
  · apply ofFiniteOrder_compatible
    exact RelativeWeighted.projection_action (old X G p) new hbalanced q
  · exact hOld
  · exact (labelled_translation_exact I q hq n hn).1

/-- Weighted relative identities and embedded torsion-free factors imply a
torsion-free presented group. All presentations and relator families are arbitrary. -/
theorem torsionFree_of_weighted
    (φ : ∀ a, G a →* Quotient X G p new)
    (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
      (φ a).comp (p a))
    (hp : ∀ a, Function.Surjective (p a)) (hφ : ∀ a, Function.Injective (φ a))
    [∀ a, IsMulTorsionFree (G a)]
    (hbalanced : Weighted.Balanced (all X G p new) (quotient X G p new)
      RelativeWeighted.newLabel) : IsMulTorsionFree (Quotient X G p new) := by
  apply torsionFree_quotient_of_relation_evenExact
  intro q hq
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq.orderOf_pos)
  change orderOf q = n + 1 at hn
  have he := relation_evenExact_of_old X G p new hbalanced q hq n hn
    (oldAction_evenExact_of_torsionFree_factors X G p new φ compat hp hφ q hq n hn
      (oldAction_period_of_pow X G p new q (n + 1)
        (by rw [← hn]; exact pow_orderOf_eq_one _)))
  simpa only [RelationAbelianization.periodic, hn] using he

end SmallPresentationStatements.RelationDerivative.FactorSplitting
