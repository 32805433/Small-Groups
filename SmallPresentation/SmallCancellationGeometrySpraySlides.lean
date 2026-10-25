module

public import SmallPresentation.FreeGroupCentralizerPeiffer

/-!
# Explicit slides of based relator occurrences

Dragging a based path past a whole block of relator discs conjugates its occurrence by the
ordered value of that block. The block itself is unchanged. This module realizes that finite
operation by elementary Peiffer exchanges and proves cancellation of a nonadjacent inverse
pair with the resulting transported path. The transport equation is explicit; an arc in a
ribbon map is not silently assumed to supply it.
-/

@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.Peiffer

variable {F Q I J : Type} [Group F] [Group Q]
    (rel : I → F) (q : F →* Q) (label : I → Option J)

/-- Left multiplication of the path to one indexed signed occurrence. -/
def transport (w : F) (a : Occurrence F I) : Occurrence F I :=
  ((w * a.1.1, a.1.2), a.2)

@[simp] theorem transport_one (a : Occurrence F I) : transport (1 : F) a = a := by
  rcases a with ⟨⟨u, i⟩, ε⟩
  simp [transport]

theorem transport_mul (u v : F) (a : Occurrence F I) :
    transport u (transport v a) = transport (u * v) a := by
  simp only [transport, mul_assoc]

theorem term_transport (w : F) (a : Occurrence F I) :
    term rel (transport w a) = w * term rel a * w⁻¹ := by
  rcases a with ⟨⟨u, i⟩, ε⟩
  cases ε <;> simp only [transport, term, Bool.cond_false, Bool.cond_true] <;>
    group

/-- Peiffer equivalence can be performed inside a fixed prefix and suffix. -/
theorem Equiv.context {u v : Sequence F I} (h : Equiv rel u v) (s t : Sequence F I) :
    Equiv rel (s ++ u ++ t) (s ++ v ++ t) := by
  induction h with
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | exchange u v a b =>
    simpa only [List.append_assoc, List.cons_append] using
      Equiv.exchange (rel := rel) (s ++ u) (v ++ t) a b
  | cancel u v a =>
    simpa only [List.append_assoc, List.cons_append] using
      Equiv.cancel (rel := rel) (s ++ u) (v ++ t) a

/-- Move an occurrence left across a whole ordered block by actual elementary exchanges. -/
theorem Equiv.slide_left (m : Sequence F I) (b : Occurrence F I) :
    Equiv rel (m ++ [b]) (transport (evaluation rel m) b :: m) := by
  induction m with
  | nil => simpa [evaluation] using (Equiv.refl (rel := rel) [b])
  | cons a m ih =>
    have h₁ := Equiv.context rel ih [a] []
    have h₂ := Equiv.exchange (rel := rel) [] m a (transport (evaluation rel m) b)
    have ht : Peiffer.exchange rel a (transport (evaluation rel m) b) =
        transport (evaluation rel (a :: m)) b := by
      change transport (term rel a) (transport (evaluation rel m) b) = _
      rw [transport_mul]
      rfl
    have hh := Equiv.trans (by simpa using h₁) h₂
    simpa only [List.nil_append, List.cons_append, ht] using hh

/-- The same path slide inside an arbitrary surrounding identity sequence. -/
theorem Equiv.slide_left_context (s m t : Sequence F I) (b : Occurrence F I) :
    Equiv rel (s ++ m ++ b :: t)
      (s ++ transport (evaluation rel m) b :: (m ++ t)) := by
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    Equiv.context rel (Equiv.slide_left rel m b) s t

/-- Complete relator blocks have trivial image in the relator quotient. -/
theorem quotient_evaluation (hkill : ∀ i, q (rel i) = 1) (s : Sequence F I) :
    q (evaluation rel s) = 1 := by
  induction s with
  | nil => exact q.map_one
  | cons a s ih =>
    change q (term rel a * evaluation rel s) = 1
    rw [map_mul, quotient_term rel q hkill, ih, one_mul]

/-- Sliding past a relator block retains the actual indexed label, sign and quotient path. -/
theorem matched_transport_evaluation (hkill : ∀ i, q (rel i) = 1)
    (m : Sequence F I) (b : Occurrence F I) :
    Matched q label (transport (evaluation rel m) b) b := by
  refine ⟨rfl, rfl, fun _ ↦ ?_⟩
  change q (evaluation rel m * b.1.1) = q b.1.1
  rw [map_mul, quotient_evaluation rel q hkill, one_mul]

/-- Cancel two same-labelled root-free occurrences separated by a block, after transporting
the second path across that block. The intervening occurrences themselves remain unchanged. -/
theorem based_cancel_across [IsFreeGroup F]
    (s m t : Sequence F I) (a b : Occurrence F I) (hi : a.1.2 = b.1.2)
    (hr : FreeGroupCentralizer.RootFree (rel a.1.2)) (hkill : q (rel a.1.2) = 1)
    (hpair : term rel a *
      (evaluation rel m * term rel b * (evaluation rel m)⁻¹) = 1) :
    BasedEquiv rel q label (s ++ a :: (m ++ b :: t)) (s ++ m ++ t) := by
  have hs := Equiv.slide_left_context rel (s ++ [a]) m t b
  have hc := FreeGroupCentralizer.based_cancel_of_same_label rel q label s (m ++ t)
    a (transport (evaluation rel m) b) hi hr hkill
    (by rw [term_transport]; exact hpair)
  apply BasedEquiv.trans (BasedEquiv.peiffer (by simpa [List.append_assoc] using hs))
  simpa only [List.append_assoc] using hc

end SmallPresentationStatements.RelationCoordinates.Peiffer
