module

public import SmallPresentation.FreeGroupCentralizerRoots
public import SmallPresentation.BasedIdentityReduction

/-! Equal labelled free-group terms retain their signs and quotient weights.
These lemmas supply the nontrivial matching witness for changed sprays/basepoints. -/
@[expose] public section

namespace SmallPresentationStatements.FreeGroupCentralizer

variable {F Q I J : Type} [Group F] [IsFreeGroup F] [Group Q]
    (rel : I → F) (q : F →* Q) (label : I → Option J)

open RelationCoordinates.Peiffer

/-- Two conjugates of a nonidentity element cannot be inverse to one another. -/
theorem conjugates_not_inverse (r : F) (hr : r ≠ 1) (u v : F) :
    u * r * u⁻¹ ≠ (v * r * v⁻¹)⁻¹ := by
  intro h
  apply conjugate_ne_inv r hr (v⁻¹ * u)
  have he := congrArg (fun t : F ↦ v⁻¹ * t * v) h
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left,
    inv_mul_cancel_right, inv_mul_cancel, mul_one] using he

/-- If labelled occurrences of a nonidentity free-group relator have equal values,
their signs agree. -/
theorem occurrence_sign_eq (a b : Occurrence F I) (hi : a.1.2 = b.1.2)
    (hr : rel a.1.2 ≠ 1) (ht : term rel a = term rel b) : a.2 = b.2 := by
  rcases a with ⟨⟨u, i⟩, s⟩
  rcases b with ⟨⟨v, j⟩, t⟩
  change i = j at hi
  subst j
  cases s <;> cases t
  · rfl
  · exact False.elim (conjugates_not_inverse (rel i) hr v u (by simpa [term] using ht.symm))
  · exact False.elim (conjugates_not_inverse (rel i) hr u v (by simpa [term] using ht))
  · rfl

/-- The based matching requirement follows from equality of labelled terms
whenever the relator is root-free and vanishes in the quotient. -/
theorem matched_of_term_eq (a b : Occurrence F I) (hi : a.1.2 = b.1.2)
    (hr : RootFree (rel a.1.2)) (hkill : q (rel a.1.2) = 1)
    (ht : term rel a = term rel b) : Matched q label a b := by
  have hs := occurrence_sign_eq rel a b hi hr.ne_one ht
  refine ⟨hi, hs, fun _ ↦ ?_⟩
  rcases a with ⟨⟨u, i⟩, s⟩
  rcases b with ⟨⟨v, j⟩, t⟩
  change i = j at hi
  change s = t at hs
  subst j
  subst t
  apply conjugator_image_eq q hr hkill
  cases s with
  | false => exact inv_injective ht
  | true => exact ht

/-- Cancel an inverse pair with the same root-free label even when its two
conjugators were chosen independently. -/
theorem based_cancel_of_same_label (s t : Sequence F I) (a b : Occurrence F I)
    (hi : a.1.2 = b.1.2) (hr : RootFree (rel a.1.2)) (hkill : q (rel a.1.2) = 1)
    (hprod : term rel a * term rel b = 1) :
    BasedEquiv rel q label (s ++ a :: b :: t) (s ++ t) := by
  have hb : term rel b = term rel (inverse a) := by
    rw [term_inverse]
    have h := congrArg Inv.inv (mul_eq_one_iff_eq_inv.mp hprod)
    simpa only [inv_inv] using h.symm
  have hm : Matched q label b (inverse a) := by
    apply matched_of_term_eq rel q label b (inverse a) hi.symm
    · simpa only [hi] using hr
    · simpa only [hi] using hkill
    · exact hb
  have hself (l : Sequence F I) : List.Forall₂ (Matched q label) l l := by
    induction l with
    | nil => exact .nil
    | cons c l ih => exact .cons ⟨rfl, rfl, fun _ ↦ rfl⟩ ih
  apply BasedEquiv.trans (t := s ++ a :: inverse a :: t) ?_
    (BasedEquiv.peiffer (RelationCoordinates.Peiffer.Equiv.cancel s t a))
  apply BasedEquiv.matched
  · induction s with
    | nil => exact .cons ⟨rfl, rfl, fun _ ↦ rfl⟩ (.cons hm (hself t))
    | cons c s ih => exact .cons ⟨rfl, rfl, fun _ ↦ rfl⟩ ih
  · change evaluation rel (s ++ ([a, b] ++ t)) =
      evaluation rel (s ++ ([a, inverse a] ++ t))
    simp only [evaluation_append]
    have he : evaluation rel [a, b] = evaluation rel [a, inverse a] := by
      simp only [evaluation, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, term_inverse, mul_inv_cancel, hprod]
    rw [he]

end SmallPresentationStatements.FreeGroupCentralizer
