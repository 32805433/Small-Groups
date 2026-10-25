module

public import SmallPresentation.SmallCancellationDipoleRelativeFactorRotation

/-! Unchanged marked and new vertex readings through factor-disc replacement rotations. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling

open PermutationCycles

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}
    (L : RibbonLabelling P X H) (τ : Equiv.Perm D) (d : D)
    (hagree : ∀ e, P.rotation.SameCycle d e → τ e = P.rotation e)
include hagree

/-- A retained vertex keeps its entire ordered original departure list. -/
theorem withRotation_vertexBoundary :
    (P.withRotation τ).vertexBoundary d = P.vertexBoundary d := by
  symm
  apply ((cycleBoundary_walk P.rotation d).changePerm ?_).eq_cycleBoundary
    (cycleBoundary_ne_nil P.rotation d) (cycleBoundary_nodup P.rotation d)
  intro e he
  apply hagree e
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp he
  exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)

omit [Group H] in
/-- Exact complete forward reading at every untouched marked or new vertex. -/
theorem withRotation_vertexWord : (L.withRotation τ).vertexWord d = L.vertexWord d := by
  change (((P.withRotation τ).vertexBoundary d).map (fun e ↦ (L.arc e, L.corner e))) = _
  rw [withRotation_vertexBoundary τ d hagree]
  rfl

omit [Finite D] in
/-- Exact inverse rotation iterates at a retained original vertex. -/
theorem withRotation_inverse_iterate (n : ℕ) : τ.symm^[n] d = P.rotation.symm^[n] d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    apply τ.injective
    rw [Equiv.apply_symm_apply, hagree _ ?_, Equiv.apply_symm_apply]
    apply Equiv.Perm.SameCycle.of_inv
    have hc : (P.rotation⁻¹).SameCycle d (((P.rotation⁻¹) ^ (n + 1)) d) :=
      Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_inv, Function.iterate_succ_apply'] using hc

/-- Exact complete backwards reading, including the shifted inverse corner coefficients. -/
theorem withRotation_reverseVertexWord :
    (L.withRotation τ).reverseVertexWord d = L.reverseVertexWord d := by
  have hp : Function.minimalPeriod τ d = Function.minimalPeriod P.rotation d := by
    simpa only [RibbonMap.vertexBoundary_length, RibbonMap.withRotation] using
      congrArg List.length (withRotation_vertexBoundary τ d hagree)
  simp only [reverseVertexWord, withRotation, RibbonMap.withRotation, hp]
  apply congrArg List.ofFn
  funext k
  change (reverseLetter (L.arc (τ.symm^[k.val] d)),
    (L.corner (τ.symm^[k.val + 1] d))⁻¹) = _
  rw [withRotation_inverse_iterate τ d hagree, withRotation_inverse_iterate τ d hagree]

section ArbitraryRetained

variable {P' : RibbonMap D} (M : RibbonLabelling P' X H)
    (hr : ∀ e, P.rotation.SameCycle d e → P'.rotation e = P.rotation e)
    (ha : ∀ e, P.rotation.SameCycle d e → M.arc e = L.arc e)
    (hc : ∀ e, P.rotation.SameCycle d e → M.corner e = L.corner e)
omit hagree
include hr

/-- Arbitrary surgery retaining a complete vertex retains its exact cyclic departure list. -/
theorem retained_vertexBoundary : P'.vertexBoundary d = P.vertexBoundary d :=
  withRotation_vertexBoundary P'.rotation d hr

/-- A retained vertex has precisely the same actual orbit after surgery. -/
theorem retained_sameCycle (e : D) :
    P'.rotation.SameCycle d e ↔ P.rotation.SameCycle d e := by
  rw [← P'.mem_vertexBoundary_iff, retained_vertexBoundary d hr, P.mem_vertexBoundary_iff]

include ha hc

omit [Group H] in
/-- Exact forward reading of a vertex whose rotation and labels are retained. -/
theorem retained_vertexWord : M.vertexWord d = L.vertexWord d := by
  unfold vertexWord
  rw [retained_vertexBoundary d hr]
  apply List.map_congr_left
  intro e he
  have h := (P.mem_vertexBoundary_iff d e).mp he
  rw [ha e h, hc e h]

/-- Exact backward reading of a retained vertex, including predecessor corner coefficients. -/
theorem retained_reverseVertexWord : M.reverseVertexWord d = L.reverseVertexWord d := by
  have hp : Function.minimalPeriod P'.rotation d = Function.minimalPeriod P.rotation d := by
    simpa only [RibbonMap.vertexBoundary_length] using
      congrArg List.length (retained_vertexBoundary d hr)
  have hi (n : ℕ) : P'.rotation.symm^[n] d = P.rotation.symm^[n] d :=
    withRotation_inverse_iterate P'.rotation d hr n
  have hcyc (n : ℕ) : P.rotation.SameCycle d (P.rotation.symm^[n] d) := by
    apply Equiv.Perm.SameCycle.of_inv
    have h : (P.rotation⁻¹).SameCycle d (((P.rotation⁻¹) ^ n) d) :=
      Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_inv] using h
  simp only [reverseVertexWord, hp]
  apply congrArg List.ofFn
  funext k
  simp only [Fin.val_cast]
  rw [hi, hi, ha _ (hcyc _), hc _ (hcyc _)]

end ArbitraryRetained

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling
