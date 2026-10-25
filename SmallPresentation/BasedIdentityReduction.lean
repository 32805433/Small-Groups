module

public import SmallPresentation.PeifferIdentities

/-!
# Based changes of identity sequences

This enlarges elementary Peiffer moves by the exact label, sign, and quotient-root
bookkeeping needed when sprays and admissible relator basepoints are changed. It
proves the weighted invariant, without assuming that a geometric reduction exists.
-/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.Peiffer

variable {F Q I J : Type} [Group F] [Group Q]
    (rel : I → F) (q : F →* Q) (label : I → Option J)

/-- Matched occurrences retain their label and sign. Selected relators also retain
 the quotient image of their conjugator; unselected relators impose no such condition. -/
def Matched (a b : Occurrence F I) : Prop :=
  a.1.2 = b.1.2 ∧ a.2 = b.2 ∧ (label a.1.2 ≠ none → q a.1.1 = q b.1.1)

/-- Root powers do not change selected coordinates when the selected roots die in the quotient. -/
theorem matched_of_root_power (root : I → F)
    (hroot : ∀ i, label i ≠ none → q (root i) = 1)
    (a b : Occurrence F I) (hi : a.1.2 = b.1.2) (hs : a.2 = b.2)
    (n : ℤ) (hq : q a.1.1 = q b.1.1 * q (root a.1.2) ^ n) :
    Matched q label a b := by
  refine ⟨hi, hs, fun hlabel ↦ ?_⟩
  simpa [hroot _ hlabel] using hq

/-- Matching carries precisely the coefficient information used by the relation module. -/
theorem weight_matched {a b : Occurrence F I} (h : Matched q label a b) :
    weight q label a = weight q label b := by
  rcases a with ⟨⟨f, i⟩, s⟩
  rcases b with ⟨⟨g, j⟩, t⟩
  rcases h with ⟨hi, hs, hq⟩
  change i = j at hi
  change s = t at hs
  subst j
  subst t
  by_cases hl : label i = none
  · cases s <;> simp [weight, Weighted.generator, hl]
  · have he : q f = q g := hq hl
    cases s <;> simp [weight, he]

/-- A termwise matching preserves the total weighted vector. -/
theorem weights_matched {s t : Sequence F I} (h : List.Forall₂ (Matched q label) s t) :
    weights q label s = weights q label t := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    change weight q label _ + weights q label _ = weight q label _ + weights q label _
    rw [weight_matched q label hab, ih]

/-- The sequence equivalence used after changing sprays and admissible basepoints.
Every non-Peiffer constructor explicitly preserves the ordered group product. -/
inductive BasedEquiv : Sequence F I → Sequence F I → Prop
  | refl (s) : BasedEquiv s s
  | symm {s t} : BasedEquiv s t → BasedEquiv t s
  | trans {s t u} : BasedEquiv s t → BasedEquiv t u → BasedEquiv s u
  | peiffer {s t} : Equiv rel s t → BasedEquiv s t
  | matched {s t} : List.Forall₂ (Matched q label) s t →
      evaluation rel s = evaluation rel t → BasedEquiv s t
  | perm {s t} : s.Perm t → evaluation rel s = evaluation rel t → BasedEquiv s t
  | reindexed {s u t} : s.Perm u → List.Forall₂ (Matched q label) u t →
      evaluation rel s = evaluation rel t → BasedEquiv s t

/-- The enlarged equivalence still preserves the literal evaluated group element. -/
theorem evaluation_basedEquiv {s t : Sequence F I} (h : BasedEquiv rel q label s t) :
    evaluation rel s = evaluation rel t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | peiffer hp => exact evaluation_equiv rel hp
  | matched _ he => exact he
  | perm _ he => exact he
  | reindexed _ _ he => exact he

/-- The weighted invariant survives all permitted based sequence changes. -/
theorem weights_basedEquiv (hkill : ∀ i, q (rel i) = 1) {s t : Sequence F I}
    (h : BasedEquiv rel q label s t) : weights q label s = weights q label t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | peiffer hp => exact weights_equiv rel q label hkill hp
  | matched hm _ => exact weights_matched q label hm
  | perm hp _ => exact (hp.map (weight q label)).sum_eq
  | reindexed hp hm _ =>
    exact ((hp.map (weight q label)).sum_eq).trans (weights_matched q label hm)

/-- The old-relator reduction interface yields the precise weighted identity hypothesis. -/
theorem balanced_of_basedReduction (hkill : ∀ i, q (rel i) = 1)
    (hreduce : ∀ s : Sequence F I, evaluation rel s = 1 →
      ∃ t, BasedEquiv rel q label s t ∧ ∀ a ∈ t, label a.1.2 = none) :
    Weighted.Balanced rel q label := by
  intro w hw
  induction w using Quot.inductionOn with
  | h s =>
    obtain ⟨t, ht, hold⟩ := hreduce s ((evaluation_mk rel s).symm.trans hw)
    change Weighted.vector q label (FreeGroup.mk s) = 1
    apply Multiplicative.toAdd.injective
    rw [vector_mk, weights_basedEquiv rel q label hkill ht,
      weights_eq_zero_of_unselected q label t hold]
    rfl

end SmallPresentationStatements.RelationCoordinates.Peiffer
