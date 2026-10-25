module

public import SmallPresentation.RelationDerivativeCyclicCoordinates

/-! Old relation summands have exact finite-cyclic periodic complexes when their
coset representatives are chosen in regular cyclic orbits. -/
@[expose] public section

namespace SmallPresentationStatements.RelationDerivative.FactorSplitting

open DirectSum RelationCoordinates
attribute [local instance] Classical.propDecidable

variable {A I : Type} (X : A → Type) (G : A → Type) [∀ a, Group (G a)]
  (p : ∀ a, FreeGroup (X a) →* G a) (new : I → FreeGroup (Σ a, X a))
  (φ : ∀ a, G a →* Quotient X G p new)
  (compat : ∀ a, (quotient X G p new).comp (FreeGroup.map (Sigma.mk a)) =
    (φ a).comp (p a))
  (B : A → Type) (n : ℕ)
  (rep : ∀ a, B a × Fin (n + 1) → Quotient X G p new)
  (hrep : ∀ a, Function.Bijective (fun z : (B a × Fin (n + 1)) × G a ↦ rep a z.1 * φ a z.2))

/-- Representatives indexed by a cyclic orbit and a position in that orbit. -/
abbrev cyclicCosets (a : A) : CosetData (φ a) where
  Index := B a × Fin (n + 1)
  representative := rep a
  bijective := hrep a

variable (q : Quotient X G p new)
  (hstep : ∀ a b j, q * rep a (b, finRotate (n + 1) j) = rep a (b, j))

include hstep in
/-- The old coset sum intertwines tuple rotation with actual quotient conjugation. -/
theorem cosetSum_cyclicAction
    (z : CyclicCoordinates.Sum B (fun a ↦ Additive (Abelianization (p a).ker)) n) :
    cosetSum X G p new φ compat (cyclicCosets X G p new φ B n rep hrep)
      (CyclicCoordinates.action B (fun a ↦ Additive (Abelianization (p a).ker)) n z) =
      RelationAbelianization.quotientAction (Relations X G p new) q
        (cosetSum X G p new φ compat (cyclicCosets X G p new φ B n rep hrep) z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i z =>
    rcases i with ⟨a, b, j⟩
    rw [CyclicCoordinates.action_of]
    have hr : (cyclicCosets X G p new φ B n rep hrep a).representative
        (b, (finRotate (n + 1)).symm j) =
        q * (cyclicCosets X G p new φ B n rep hrep a).representative (b, j) := by
      change rep a (b, (finRotate (n + 1)).symm j) = q * rep a (b, j)
      simpa only [Equiv.apply_symm_apply] using
        (hstep a b ((finRotate (n + 1)).symm j)).symm
    convert! (quotientAction_cosetSum_of X G p new φ compat
      (cyclicCosets X G p new φ B n rep hrep) q a (b, j)
      (b, (finRotate (n + 1)).symm j) hr z).symm using 1
    · congr 1
      apply DirectSum.ext
      intro k
      simp only [DirectSum.of_apply]
    · congr 2
      apply DirectSum.ext
      intro k
      simp only [DirectSum.of_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Actual quotient action on the invariant old-relator image. -/
noncomputable def oldAction : AddMonoid.End (RelativeWeighted.oldMap (old X G p) new).range :=
  ((RelationAbelianization.quotientAction (Relations X G p new) q).comp
    (RelativeWeighted.oldMap (old X G p) new).range.subtype).codRestrict _ (by
      rintro ⟨z, hz⟩
      obtain ⟨v, rfl⟩ := hz
      exact ⟨Weighted.shift q v, RelativeWeighted.oldMap_shift (old X G p) new q v⟩)

@[simp] theorem oldAction_val (z : (RelativeWeighted.oldMap (old X G p) new).range) :
    (oldAction X G p new q z).val =
      RelationAbelianization.quotientAction (Relations X G p new) q z.val := rfl

variable (hp : ∀ a, Function.Surjective (p a))

include hstep in
/-- The isomorphism to the old image preserves the actual action. -/
theorem cosetSumEquiv_cyclicAction
    (z : CyclicCoordinates.Sum B (fun a ↦ Additive (Abelianization (p a).ker)) n) :
    cosetSumEquiv X G p new φ compat (cyclicCosets X G p new φ B n rep hrep) hp
      (CyclicCoordinates.action B (fun a ↦ Additive (Abelianization (p a).ker)) n z) =
      oldAction X G p new q
        (cosetSumEquiv X G p new φ compat (cyclicCosets X G p new φ B n rep hrep) hp z) := by
  apply Subtype.ext
  exact cosetSum_cyclicAction X G p new φ compat B n rep hrep q hstep z

include φ compat B rep hrep hstep hp in
/-- The old action has the specified finite period. -/
theorem oldAction_period : oldAction X G p new q ^ (n + 1) = 1 := by
  apply AddMonoid.End.ext
  intro z
  obtain ⟨v, rfl⟩ := (cosetSumEquiv X G p new φ compat
    (cyclicCosets X G p new φ B n rep hrep) hp).surjective z
  have h := CyclicModule.commute_powers
    (CyclicCoordinates.action B (fun a ↦ Additive (Abelianization (p a).ker)) n)
    (oldAction X G p new q)
    (cosetSumEquiv X G p new φ compat (cyclicCosets X G p new φ B n rep hrep) hp).toAddMonoidHom
    (cosetSumEquiv_cyclicAction X G p new φ compat B n rep hrep q hstep hp) (n + 1) v
  rw [CyclicCoordinates.action_period] at h
  exact h.symm

/-- Both cyclic parities are exact on the old relation image, without any
freeness or finiteness restriction on the factor relation coefficient groups. -/
theorem oldAction_exact :
    (CyclicModule.ofFiniteOrder (oldAction X G p new q) (n + 1)
      (oldAction_period X G p new φ compat B n rep hrep q hstep hp)).EvenExact ∧
    (CyclicModule.ofFiniteOrder (oldAction X G p new q) (n + 1)
      (oldAction_period X G p new φ compat B n rep hrep q hstep hp)).OddExact := by
  let e := cosetSumEquiv X G p new φ compat (cyclicCosets X G p new φ B n rep hrep) hp
  have hc := CyclicModule.ofFiniteOrder_compatible
    (CyclicCoordinates.action B (fun a ↦ Additive (Abelianization (p a).ker)) n)
    (oldAction X G p new q) (n + 1)
    (CyclicCoordinates.action_period B (fun a ↦ Additive (Abelianization (p a).ker)) n)
    (oldAction_period X G p new φ compat B n rep hrep q hstep hp)
    e.toAddMonoidHom (cosetSumEquiv_cyclicAction X G p new φ compat B n rep hrep q hstep hp)
  exact ⟨CyclicModule.Periodic.evenExact_of_equiv _ _ e hc
      (CyclicCoordinates.action_exact B (fun a ↦ Additive (Abelianization (p a).ker)) n).1,
    CyclicModule.Periodic.oddExact_of_equiv _ _ e hc
      (CyclicCoordinates.action_exact B (fun a ↦ Additive (Abelianization (p a).ker)) n).2⟩

end SmallPresentationStatements.RelationDerivative.FactorSplitting
