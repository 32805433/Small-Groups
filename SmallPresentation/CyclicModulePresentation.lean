module

public import SmallPresentation.CyclicModuleGroupOrbit
public import SmallPresentation.RelationDerivativeEquivariance

/-! A torsion obstruction for arbitrary group presentations, stated using the actual
conjugation action on their relation modules. The vertex and edge periodic complexes
are proved exact by decomposing their bases into finite cyclic orbits. -/
@[expose] public section

namespace SmallPresentationStatements.CyclicModule

open RelationDerivative

variable {X H : Type} [Group H] (p : FreeGroup X →* H)

/-- The actual quotient-group action on the abelianized presentation kernel. -/
noncomputable def presentationAction (hp : Function.Surjective p) (c : H) :
    AddMonoid.End (Additive (Abelianization p.ker)) := relationShift p hp c

theorem presentationAction_pow (hp : Function.Surjective p) (c : H) (k : ℕ)
    (a : Additive (Abelianization p.ker)) :
    (presentationAction p hp c ^ k) a = relationShift p hp (c ^ k) a := by
  induction k with
  | zero =>
    change a = relationShift p hp (c ^ 0) a
    rw [pow_zero, relationShift_one]
  | succ k ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih]
    change relationShift p hp c (relationShift p hp (c ^ k) a) = _
    rw [← relationShift_mul, pow_succ']

theorem presentationAction_pow_order (hp : Function.Surjective p) (c : H) :
    presentationAction p hp c ^ orderOf c = 1 := by
  apply AddMonoid.End.ext
  intro a
  rw [presentationAction_pow, pow_orderOf_eq_one, relationShift_one]
  rfl

/-- The periodic complex attached to a finite-order element and the presentation kernel. -/
noncomputable def presentationPeriodic (hp : Function.Surjective p) (c : H) :
    Periodic (Additive (Abelianization p.ker)) :=
  ofFiniteOrder (presentationAction p hp c) (orderOf c)
    (presentationAction_pow_order p hp c)

theorem augmentation_vertexShift (c : H) (v : Vertices H) :
    augmentation (vertexShift c v) = augmentation v := by
  induction v using FreeAbelianGroup.induction_on with
  | zero => simp
  | of h => simp [vertexShift, FreeAbelianGroup.map_of_apply, augmentation_of]
  | neg h => simp_all only [map_neg]
  | add a b ha hb => simp_all only [map_add]

/-- A nontrivial finite-order element cannot have an even-exact relation-module complex. -/
theorem presentation_finite_order_obstruction (hp : Function.Surjective p)
    (c : H) (hc : IsOfFinOrder c) (horder : 1 < orderOf c)
    (hrel : (presentationPeriodic p hp c).EvenExact) : False := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc.orderOf_pos)
  change orderOf c = n + 1 at hn
  let tB := permutationAction (labelledTranslation X c)
  let tC := permutationAction (leftTranslation c)
  have hB : tB ^ (n + 1) = 1 := permutation_pow_order n
    (labelledOrbitCoordinates X c hc n hn) (labelledTranslation X c)
    (labelledOrbitCoordinates_step X c hc n hn)
  have hC : tC ^ (n + 1) = 1 := permutation_pow_order n
    (groupOrbitCoordinates c hc n hn) (leftTranslation c)
    (groupOrbitCoordinates_step c hc n hn)
  have hA : presentationAction p hp c ^ (n + 1) = 1 := by
    rw [← hn]; exact presentationAction_pow_order p hp c
  have hrel' : (ofFiniteOrder (presentationAction p hp c) (n + 1) hA).EvenExact := by
    simpa only [presentationPeriodic, hn] using hrel
  obtain ⟨hi, hij, hjp, hsurj⟩ := presentation_exact p hp
  apply Periodic.integer_obstruction (n + 1) (by omega)
    (ofFiniteOrder (presentationAction p hp c) (n + 1) hA)
    (ofFiniteOrder tB (n + 1) hB) (ofFiniteOrder tC (n + 1) hC)
    (relationDerivative p) (boundary p) augmentation hi hij hjp hsurj
  · apply ofFiniteOrder_compatible
    exact relationDerivative_shift p hp c
  · apply ofFiniteOrder_compatible
    exact boundary_shift p c
  · apply ofFiniteOrder_integer_compatible
    exact augmentation_vertexShift c
  · exact hrel'
  · exact (labelled_translation_exact X c hc n hn).2
  · exact (group_translation_exact c hc n hn).1

/-- A presentation defines a torsion-free group if the actual relation module is
even-exact for every finite cyclic restriction. No finiteness assumptions are imposed
on the group or its generating set. -/
theorem torsionFree_of_presentation_evenExact (hp : Function.Surjective p)
    (hrel : ∀ c : H, IsOfFinOrder c → (presentationPeriodic p hp c).EvenExact) :
    IsMulTorsionFree H := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro c hc hfin
  apply presentation_finite_order_obstruction p hp c hfin _ (hrel c hfin)
  have hpos := hfin.orderOf_pos
  have hne : orderOf c ≠ 1 := fun he => hc (orderOf_eq_one_iff.mp he)
  omega

end SmallPresentationStatements.CyclicModule
