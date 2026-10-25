module

public import SmallPresentation.SmallCancellationGeometryRibbon
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Noncrossing inverse-letter pairings of freely trivial boundary words

An adjacent inverse-pair insertion is a combinatorial cap insertion in a disc collar. Starting
from the empty boundary, a finite sequence of these operations gives an explicit list of paired
positions. The positions are ordered, noncrossing, and carry opposite labels. Every freely trivial
word admits such a certificate by the free-group reduction theorem. This is the boundary-folding
part of picture realization, not a claim that relator discs or sprays have already been constructed.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {X : Type*}

/-- A finite cap-insertion certificate on a specified boundary word. The constructor inserts
adjacent inverse letters at any gap in the current boundary, preserving all old pairings. -/
inductive BoundaryPairing : List (SignedLetter X) → Type _
  | empty : BoundaryPairing []
  | insert (before after : List (SignedLetter X)) (x : X) (sign : Bool)
      (old : BoundaryPairing (before ++ after)) :
      BoundaryPairing (before ++ (x, sign) :: (x, !sign) :: after)

namespace BoundaryPairing

/-- Shift an old position past two newly inserted boundary positions. -/
def shift (gap i : ℕ) : ℕ := if i < gap then i else i + 2

theorem shift_lt_shift_iff (gap i j : ℕ) : shift gap i < shift gap j ↔ i < j := by
  unfold shift
  split_ifs <;> omega

theorem shift_injective (gap : ℕ) : Function.Injective (shift gap) := by
  intro i j h
  unfold shift at h
  split_ifs at h <;> omega

theorem shift_ne_gap (gap i : ℕ) : shift gap i ≠ gap := by
  unfold shift
  split_ifs <;> omega

theorem shift_ne_gap_succ (gap i : ℕ) : shift gap i ≠ gap + 1 := by
  unfold shift
  split_ifs <;> omega

theorem shift_lt_length (gap n i : ℕ) (hi : i < n) : shift gap i < n + 2 := by
  unfold shift
  split_ifs <;> omega

/-- Move both ends of an existing arc past the inserted cap. -/
def shiftArc (gap : ℕ) (arc : ℕ × ℕ) : ℕ × ℕ := (shift gap arc.1, shift gap arc.2)

/-- Actual paired boundary positions, one ordered pair for each inserted cap. -/
def arcs : {w : List (SignedLetter X)} → BoundaryPairing w → List (ℕ × ℕ)
  | _, .empty => []
  | _, .insert before _ _ _ old =>
      (before.length, before.length + 1) :: (arcs old).map (shiftArc before.length)

/-- The number of actual cap arcs is half the number of boundary positions. -/
theorem twice_arcs_length {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    2 * (arcs P).length = w.length := by
  induction P with
  | empty => rfl
  | insert before after x sign old ih =>
    simp only [arcs, List.length_cons, List.length_map, List.length_append] at *
    omega

/-- Every recorded arc joins an earlier boundary position to a later one. -/
theorem arcs_ordered {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ arc ∈ arcs P, arc.1 < arc.2 := by
  induction P with
  | empty => simp [arcs]
  | insert before after x sign old ih =>
    intro arc ha
    simp only [arcs, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨oldArc, hm, rfl⟩
    · omega
    · exact (shift_lt_shift_iff _ _ _).mpr (ih oldArc hm)

/-- Both endpoints of every recorded arc lie on the actual boundary word. -/
theorem arcs_bounded {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ arc ∈ arcs P, arc.1 < w.length ∧ arc.2 < w.length := by
  induction P with
  | empty => simp [arcs]
  | insert before after x sign old ih =>
    intro arc ha
    simp only [arcs, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨oldArc, hm, rfl⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · obtain ⟨hleft, hright⟩ := ih oldArc hm
      have hl := shift_lt_length before.length (before ++ after).length oldArc.1 hleft
      have hr := shift_lt_length before.length (before ++ after).length oldArc.2 hright
      simpa only [shiftArc, List.length_append, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using And.intro hl hr

/-- Two chords cross precisely when their ordered endpoints strictly interleave. -/
def Crosses (arc other : ℕ × ℕ) : Prop :=
  arc.1 < other.1 ∧ other.1 < arc.2 ∧ arc.2 < other.2

/-- Strictly monotone shifting preserves the crossing relation exactly. -/
theorem crosses_shiftArc_iff (gap : ℕ) (arc other : ℕ × ℕ) :
    Crosses (shiftArc gap arc) (shiftArc gap other) ↔ Crosses arc other := by
  simp only [Crosses, shiftArc, shift_lt_shift_iff]

/-- The constructed chords do not cross. This is proved from the actual endpoint ordering,
not supplied as an assumption on a diagram. -/
theorem arcs_noncrossing {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ arc ∈ arcs P, ∀ other ∈ arcs P, ¬Crosses arc other := by
  induction P with
  | empty => simp [arcs]
  | insert before after x sign old ih =>
    intro arc ha other ho hc
    simp only [arcs, List.mem_cons, List.mem_map] at ha ho
    rcases ha with rfl | ⟨oldArc, ha, rfl⟩
    · unfold Crosses at hc
      omega
    · rcases ho with rfl | ⟨oldOther, ho, rfl⟩
      · unfold Crosses at hc
        omega
      · exact ih oldArc ha oldOther ho ((crosses_shiftArc_iff _ _ _).mp hc)

/-- Looking up an old position after cap insertion gives exactly its old letter. -/
theorem getElem_insert_shift (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (i : ℕ) :
    (before ++ (x, sign) :: (x, !sign) :: after)[shift before.length i]? =
      (before ++ after)[i]? := by
  by_cases hi : i < before.length
  · simp only [shift, ite_true, List.getElem?_append, hi]
  · have hi' : ¬i + 2 < before.length := by omega
    have hs : i + 2 - before.length = (i - before.length) + 2 := by omega
    simp only [shift, hi, ite_false, List.getElem?_append, hi', hs,
      List.getElem?_cons_succ]

/-- Every actual paired pair of positions carries the same generator with opposite signs. -/
theorem arcs_inverse_labels {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ arc ∈ arcs P, ∃ x sign,
      w[arc.1]? = some (x, sign) ∧ w[arc.2]? = some (x, !sign) := by
  induction P with
  | empty => simp [arcs]
  | insert before after x sign old ih =>
    intro arc ha
    simp only [arcs, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | ⟨oldArc, hm, rfl⟩
    · refine ⟨x, sign, ?_, ?_⟩ <;> simp
    · obtain ⟨y, t, hl, hr⟩ := ih oldArc hm
      refine ⟨y, t, ?_, ?_⟩
      · simpa only [shiftArc, getElem_insert_shift] using hl
      · simpa only [shiftArc, getElem_insert_shift] using hr

/-- All recorded endpoints, retaining their multiplicities for the perfect-matching proof. -/
def endpoints {w : List (SignedLetter X)} (P : BoundaryPairing w) : List ℕ :=
  (arcs P).flatMap (fun arc ↦ [arc.1, arc.2])

@[simp] theorem endpoints_empty :
    endpoints (BoundaryPairing.empty : BoundaryPairing ([] : List (SignedLetter X))) = [] := rfl

@[simp] theorem endpoints_insert (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) :
    endpoints (.insert before after x sign old) =
      before.length :: (before.length + 1) :: (endpoints old).map (shift before.length) := by
  simp [endpoints, arcs, List.flatMap_map, List.map_flatMap, shiftArc]

/-- No endpoint is used by two arcs, and no arc pairs an endpoint with itself. -/
theorem endpoints_nodup {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    (endpoints P).Nodup := by
  induction P with
  | empty => simp
  | insert before after x sign old ih =>
    rw [endpoints_insert, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_map, not_or, not_exists, not_and]
      constructor
      · omega
      · intro i _ hi
        exact shift_ne_gap before.length i hi
    · simp only [List.mem_map, not_exists, not_and]
      intro i _ hi
      exact shift_ne_gap_succ before.length i hi
    · exact ih.map (shift_injective before.length)

/-- Each original boundary position contributes one endpoint to the constructed matching. -/
theorem endpoints_length {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    (endpoints P).length = w.length := by
  induction P with
  | empty => rfl
  | insert before after x sign old ih =>
    simp only [endpoints_insert, List.length_cons, List.length_map, List.length_append] at *
    omega

theorem endpoints_bounded {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    ∀ i ∈ endpoints P, i < w.length := by
  intro i hi
  obtain ⟨arc, ha, hi⟩ := List.mem_flatMap.mp hi
  have hb := P.arcs_bounded arc ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact hb.1
  · exact hb.2

/-- The matching covers all boundary positions. Together with `endpoints_nodup` this proves
that the explicitly recorded noncrossing arcs are a perfect pairing. -/
theorem endpoints_toFinset {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    (endpoints P).toFinset = Finset.range w.length := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    exact Finset.mem_range.mpr (P.endpoints_bounded i (List.mem_toFinset.mp hi))
  · rw [List.toFinset_card_of_nodup P.endpoints_nodup, P.endpoints_length,
      Finset.card_range]

theorem mem_endpoints_iff {w : List (SignedLetter X)} (P : BoundaryPairing w) (i : ℕ) :
    i ∈ endpoints P ↔ i < w.length := by
  rw [← List.mem_toFinset, P.endpoints_toFinset, Finset.mem_range]

/-- Juxtapose two cap diagrams in disjoint boundary intervals. -/
noncomputable def append {w v : List (SignedLetter X)}
    (P : BoundaryPairing w) (Q : BoundaryPairing v) :
    BoundaryPairing (w ++ v) := by
  induction P with
  | empty => exact Q
  | insert before after x sign old ih =>
    simpa only [List.append_assoc, List.cons_append] using
      BoundaryPairing.insert before (after ++ v) x sign
        (by simpa only [List.append_assoc] using ih)

/-- Enclose an existing cap diagram by one new inverse-letter arc. -/
noncomputable def enclose (x : X) (sign : Bool)
    {w : List (SignedLetter X)} (P : BoundaryPairing w) :
    BoundaryPairing ((x, sign) :: (w ++ [(x, !sign)])) := by
  induction P with
  | empty => exact .insert [] [] x sign .empty
  | insert before after y t old ih =>
    simpa only [List.append_assoc, List.cons_append] using
      BoundaryPairing.insert ((x, sign) :: before) (after ++ [(x, !sign)]) y t
        (by simpa only [List.append_assoc, List.cons_append] using ih)

/-- A cap certificate gives an actual free reduction to the empty word. -/
theorem red_nil {w : List (SignedLetter X)} (P : BoundaryPairing w) : FreeGroup.Red w [] := by
  induction P with
  | empty => exact FreeGroup.Red.refl
  | insert before after x sign old ih =>
    exact FreeGroup.Red.trans FreeGroup.Red.Step.not.to_red ih

/-- Lift a certificate backwards across any finite free reduction. -/
theorem nonempty_of_red {w v : List (SignedLetter X)} (h : FreeGroup.Red w v) :
    Nonempty (BoundaryPairing v) → Nonempty (BoundaryPairing w) := by
  induction h with
  | refl => exact id
  | tail h step ih =>
    intro ⟨P⟩
    apply ih
    cases step with
    | @not before after x sign => exact ⟨.insert before after x sign P⟩

/-- Every word representing the identity has a finite noncrossing cap certificate. -/
theorem nonempty_of_mk_eq_one {w : List (SignedLetter X)} (h : FreeGroup.mk w = 1) :
    Nonempty (BoundaryPairing w) := by
  have h' : FreeGroup.mk w = FreeGroup.mk [] := h
  obtain ⟨v, hw, hv⟩ := FreeGroup.Red.exact.mp h'
  have he : v = [] := FreeGroup.Red.nil_iff.mp hv
  subst v
  exact nonempty_of_red hw ⟨.empty⟩

/-- The boundary-folding certificate is equivalent to free triviality. -/
theorem nonempty_iff_mk_eq_one (w : List (SignedLetter X)) :
    Nonempty (BoundaryPairing w) ↔ FreeGroup.mk w = 1 := by
  constructor
  · rintro ⟨P⟩
    exact FreeGroup.Red.exact.mpr ⟨[], P.red_nil, FreeGroup.Red.refl⟩
  · exact nonempty_of_mk_eq_one

/-- Choose a finite boundary-folding certificate from a proof of free triviality. -/
noncomputable def ofMkEqOne (w : List (SignedLetter X)) (h : FreeGroup.mk w = 1) :
    BoundaryPairing w := Classical.choice (nonempty_of_mk_eq_one h)

/-- A standalone finite noncrossing perfect matching with verified boundary labels. -/
structure Matching (w : List (SignedLetter X)) where
  pairs : List (ℕ × ℕ)
  ordered : ∀ arc ∈ pairs, arc.1 < arc.2
  bounded : ∀ arc ∈ pairs, arc.1 < w.length ∧ arc.2 < w.length
  endpoint_nodup : (pairs.flatMap (fun arc ↦ [arc.1, arc.2])).Nodup
  endpoint_coverage : (pairs.flatMap (fun arc ↦ [arc.1, arc.2])).toFinset = Finset.range w.length
  inverse_labels : ∀ arc ∈ pairs, ∃ x sign,
    w[arc.1]? = some (x, sign) ∧ w[arc.2]? = some (x, !sign)
  noncrossing : ∀ arc ∈ pairs, ∀ other ∈ pairs, ¬Crosses arc other

/-- Extract the actual matching, with all invariants proved from cap insertion. -/
def toMatching {w : List (SignedLetter X)} (P : BoundaryPairing w) : Matching w where
  pairs := P.arcs
  ordered := P.arcs_ordered
  bounded := P.arcs_bounded
  endpoint_nodup := P.endpoints_nodup
  endpoint_coverage := P.endpoints_toFinset
  inverse_labels := P.arcs_inverse_labels
  noncrossing := P.arcs_noncrossing

/-- Complete boundary pairing for an arbitrary freely trivial word. -/
noncomputable def matchingOfMkEqOne (w : List (SignedLetter X)) (h : FreeGroup.mk w = 1) :
    Matching w := (ofMkEqOne w h).toMatching

end BoundaryPairing
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
