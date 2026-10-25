module

public import SmallPresentation.SmallCancellationGeometryPairingRibbon
public import SmallPresentation.SmallCancellationGeometryRibbonCounts
public import SmallPresentation.PermutationCycles

/-! Exact dart coordinates for inserting a cap into a boundary pairing. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing

namespace CapCoordinates

/-- Old boundary positions and the two new cap ends in their actual cyclic order. -/
def embed {n : ℕ} (gap : ℕ) (hg : gap ≤ n) : Fin n ⊕ Bool → Fin (n + 2)
  | .inl d => ⟨shift gap d.val, shift_lt_length gap n d.val d.isLt⟩
  | .inr false => ⟨gap, by omega⟩
  | .inr true => ⟨gap + 1, by omega⟩

@[simp] theorem embed_inl_val {n gap : ℕ} (hg : gap ≤ n) (d : Fin n) :
    (embed gap hg (.inl d)).val = shift gap d.val := rfl

@[simp] theorem embed_false_val {n gap : ℕ} (hg : gap ≤ n) :
    (embed gap hg (.inr false)).val = gap := rfl

@[simp] theorem embed_true_val {n gap : ℕ} (hg : gap ≤ n) :
    (embed gap hg (.inr true)).val = gap + 1 := rfl

theorem embed_injective {n gap : ℕ} (hg : gap ≤ n) :
    Function.Injective (embed gap hg) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext (shift_injective gap hv))
    | inr b =>
      cases b
      · exact False.elim (shift_ne_gap gap a.val hv)
      · exact False.elim (shift_ne_gap_succ gap a.val hv)
  | inr a =>
    cases b with
    | inl b =>
      cases a
      · exact False.elim (shift_ne_gap gap b.val hv.symm)
      · exact False.elim (shift_ne_gap_succ gap b.val hv.symm)
    | inr b =>
      cases a <;> cases b
      · rfl
      · change gap = gap + 1 at hv; omega
      · change gap + 1 = gap at hv; omega
      · rfl

/-- The insertion coordinates exhaust the new boundary exactly once. -/
noncomputable def equiv {n : ℕ} (gap : ℕ) (hg : gap ≤ n) :
    Fin n ⊕ Bool ≃ Fin (n + 2) :=
  Equiv.ofBijective (embed gap hg)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨embed_injective hg, by simp⟩)

@[simp] theorem equiv_apply {n gap : ℕ} (hg : gap ≤ n) (d : Fin n ⊕ Bool) :
    equiv gap hg d = embed gap hg d := rfl

/-- Numeric cyclic predecessor, including the wrap at zero. -/
theorem predecessor_val {n : ℕ} (d : Fin n) :
    ((finRotate n).symm d).val = if d.val = 0 then n - 1 else d.val - 1 := by
  have : NeZero n := d.neZero
  by_cases hd : d.val = 0
  · have hz : d = 0 := Fin.ext hd
    subst d
    by_cases hn : n = 1
    · subst n; simp
    · have hn' : 1 < n := by have := NeZero.ne n; omega
      simp [finRotate_symm_apply, Fin.neg_def, Nat.mod_eq_of_lt hn',
        Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  · have hz : d ≠ 0 := fun h ↦ hd (congrArg Fin.val h)
    rw [ite_eq_right hd]
    exact coe_finRotate_symm_of_ne_zero hz

/-- The old position immediately before the inserted cap. -/
def predecessor {n : ℕ} (gap : ℕ) (hg : gap ≤ n) (hn : 0 < n) : Fin n :=
  ⟨if gap = 0 then n - 1 else gap - 1, by split_ifs <;> omega⟩

/-- The second new dart goes directly to the old predecessor in the face permutation. -/
theorem predecessor_false {n gap : ℕ} (hg : gap ≤ n) (hn : 0 < n) :
    (finRotate (n + 2)).symm (embed gap hg (.inr false)) =
      embed gap hg (.inl (predecessor gap hg hn)) := by
  apply Fin.ext
  rw [predecessor_val]
  change (if gap = 0 then n + 2 - 1 else gap - 1) =
    shift gap (if gap = 0 then n - 1 else gap - 1)
  unfold shift
  split_ifs <;> omega

/-- The first new dart is the cyclic predecessor of the second new dart. -/
theorem predecessor_true {n gap : ℕ} (hg : gap ≤ n) :
    (finRotate (n + 2)).symm (embed gap hg (.inr true)) =
      embed gap hg (.inr false) := by
  apply Fin.ext
  rw [predecessor_val]
  simp only [embed_true_val, embed_false_val]
  simp

/-- On old darts, cyclic predecessor inserts the second cap end at exactly one position. -/
theorem predecessor_old {n gap : ℕ} (hg : gap ≤ n) (hn : 0 < n) (d : Fin n) :
    (finRotate (n + 2)).symm (embed gap hg (.inl d)) =
      if (finRotate n).symm d = predecessor gap hg hn then embed gap hg (.inr true)
      else embed gap hg (.inl ((finRotate n).symm d)) := by
  have hd := d.isLt
  have he : (finRotate n).symm d = predecessor gap hg hn ↔
      (if d.val = 0 then n - 1 else d.val - 1) =
        (if gap = 0 then n - 1 else gap - 1) := by
    rw [← Fin.val_inj, predecessor_val]
    rfl
  split_ifs with h
  · have hv := he.mp h
    apply Fin.ext
    rw [predecessor_val]
    change (if shift gap d.val = 0 then n + 2 - 1 else shift gap d.val - 1) = gap + 1
    unfold shift
    split_ifs at * <;> omega
  · have hv : (if d.val = 0 then n - 1 else d.val - 1) ≠
        (if gap = 0 then n - 1 else gap - 1) := fun hh ↦ h (he.mpr hh)
    apply Fin.ext
    rw [predecessor_val]
    change (if shift gap d.val = 0 then n + 2 - 1 else shift gap d.val - 1) =
      shift gap ((finRotate n).symm d).val
    rw [predecessor_val]
    unfold shift
    split_ifs at * <;> omega

end CapCoordinates

variable {X : Type*}

/-- Insert the two new positions while retaining the actual old word coordinates. -/
def insertPosition (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (d : Fin (before ++ after).length) :
    Fin (before ++ (x, sign) :: (x, !sign) :: after).length :=
  ⟨shift before.length d.val, by
    have h := shift_lt_length before.length (before ++ after).length d.val d.isLt
    simpa only [List.length_append, List.length_cons, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using h⟩

/-- Existing abstract arc ends are shifted past the new head arc. -/
def insertArcDart (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (d : old.ArcDart) :
    (BoundaryPairing.insert before after x sign old).ArcDart :=
  (⟨d.1.val + 1, by simpa only [arcs, List.length_cons, List.length_map]
      using Nat.succ_lt_succ d.1.isLt⟩, d.2)

/-- Inserting a cap shifts both ends of every old arc by the same boundary embedding. -/
theorem insert_position_old (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (d : old.ArcDart) :
    (BoundaryPairing.insert before after x sign old).position
      (insertArcDart before after x sign old d) =
    insertPosition before after x sign (old.position d) := by
  rcases d with ⟨i, b⟩
  apply Fin.ext
  cases b <;> simp [position, insertArcDart, insertPosition, arcs, shiftArc]

/-- The actual pairing involution on all old darts is preserved by cap insertion. -/
theorem inserted_edge_old (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (d : Fin (before ++ after).length) :
    (BoundaryPairing.insert before after x sign old).ribbon.edge
      (insertPosition before after x sign d) =
    insertPosition before after x sign (old.ribbon.edge d) := by
  obtain ⟨a, rfl⟩ := old.position_bijective.surjective d
  rw [← insert_position_old, ribbon_edge_position, ribbon_edge_position]
  exact insert_position_old before after x sign old (old.reverseDart a)

/-- Coordinates identifying old darts and the two cap ends with the new word positions. -/
noncomputable def insertEquiv (before after : List (SignedLetter X)) (x : X) (sign : Bool) :
    Fin (before ++ after).length ⊕ Bool ≃
      Fin (before ++ (x, sign) :: (x, !sign) :: after).length :=
  (CapCoordinates.equiv before.length (by simp)).trans
    (finCongr (by simp only [List.length_append, List.length_cons]; omega))

@[simp] theorem insertEquiv_old (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (d : Fin (before ++ after).length) :
    insertEquiv before after x sign (.inl d) = insertPosition before after x sign d := by
  apply Fin.ext
  rfl

@[simp] theorem insertEquiv_false (before after : List (SignedLetter X)) (x : X) (sign : Bool) :
    insertEquiv before after x sign (.inr false) = ⟨before.length, by simp⟩ := by
  apply Fin.ext
  rfl

@[simp] theorem insertEquiv_true (before after : List (SignedLetter X)) (x : X) (sign : Bool) :
    insertEquiv before after x sign (.inr true) = ⟨before.length + 1, by simp⟩ := by
  apply Fin.ext
  rfl

/-- Both ends of the inserted edge have the expected exact coordinates. -/
theorem inserted_edge_true (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) :
    (BoundaryPairing.insert before after x sign old).ribbon.edge
      (insertEquiv before after x sign (.inr true)) =
      insertEquiv before after x sign (.inr false) := by
  have he := inserted_cap_edge before after x sign old
  rw [insertEquiv_true, insertEquiv_false, ← he]
  exact (BoundaryPairing.insert before after x sign old).ribbon.edge_involutive _

/-- First cap end is a fixed point of the actual new face permutation. -/
theorem inserted_face_false (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) :
    (BoundaryPairing.insert before after x sign old).ribbon.face
      (insertEquiv before after x sign (.inr false)) =
      insertEquiv before after x sign (.inr false) := by
  apply face_fixed_of_adjacent
  · simp
  · simp only [insertEquiv_false]
    exact congrArg Fin.val (inserted_cap_edge before after x sign old)

/-- The finite-size equivalence agrees with the canonical cast on each position. -/
theorem finCongr_apply_cast {n m : ℕ} (h : n = m) (d : Fin n) :
    finCongr h d = Fin.cast h d := by
  subst m
  rfl

/-- Cyclic predecessor commutes with casting the size of a finite ordered boundary. -/
theorem predecessor_cast {n m : ℕ} (h : n = m) (d : Fin n) :
    (finRotate m).symm (Fin.cast h d) = Fin.cast h ((finRotate n).symm d) := by
  subst m
  rfl

/-- The second cap end enters the old face at the predecessor of the gap. -/
theorem inserted_face_true (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (hn : 0 < (before ++ after).length) :
    (BoundaryPairing.insert before after x sign old).ribbon.face
      (insertEquiv before after x sign (.inr true)) =
      insertEquiv before after x sign
        (.inl (CapCoordinates.predecessor before.length (by simp) hn)) := by
  change (finRotate _).symm
    ((BoundaryPairing.insert before after x sign old).ribbon.edge _) = _
  rw [inserted_edge_true]
  change (finRotate _).symm (Fin.cast (by simp only [List.length_append, List.length_cons]; omega)
      (CapCoordinates.embed before.length (by simp) (.inr false))) = _
  rw [predecessor_cast, CapCoordinates.predecessor_false _ hn]
  rfl

/-- On old darts the face successor changes precisely where the new cap was inserted. -/
theorem inserted_face_old (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (hn : 0 < (before ++ after).length)
    (d : Fin (before ++ after).length) :
    (BoundaryPairing.insert before after x sign old).ribbon.face
      (insertEquiv before after x sign (.inl d)) =
      if old.ribbon.face d = CapCoordinates.predecessor before.length (by simp) hn then
        insertEquiv before after x sign (.inr true)
      else insertEquiv before after x sign (.inl (old.ribbon.face d)) := by
  change (finRotate _).symm
    ((BoundaryPairing.insert before after x sign old).ribbon.edge _) = _
  rw [insertEquiv_old, inserted_edge_old]
  change (finRotate _).symm
    (Fin.cast (by simp only [List.length_append, List.length_cons]; omega)
      (CapCoordinates.embed before.length (by simp) (.inl (old.ribbon.edge d)))) = _
  rw [predecessor_cast]
  have hp := CapCoordinates.predecessor_old (by simp : before.length ≤
    (before ++ after).length) hn (old.ribbon.edge d)
  have hc := congrArg (Fin.cast (by
    simp only [List.length_append, List.length_cons]; omega :
      (before ++ after).length + 2 =
        (before ++ (x, sign) :: (x, !sign) :: after).length)) hp
  simpa only [apply_ite, RibbonMap.face_apply, ribbon_rotation, insertEquiv,
    Equiv.trans_apply, CapCoordinates.equiv_apply, finCongr_apply_cast] using hc

/-- The actual face permutation is the universal cap insertion permutation in these coordinates. -/
theorem inserted_face_conjugacy (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (hn : 0 < (before ++ after).length)
    (d : Fin (before ++ after).length ⊕ Bool) :
    insertEquiv before after x sign
      (PermutationCycles.capPerm old.ribbon.face
        (CapCoordinates.predecessor before.length (by simp) hn) d) =
    (BoundaryPairing.insert before after x sign old).ribbon.face
      (insertEquiv before after x sign d) := by
  rcases d with d | b
  · rw [inserted_face_old before after x sign old hn]
    split_ifs with h
    · rw [PermutationCycles.capPerm_inl_eq _ _ _ h]
    · rw [PermutationCycles.capPerm_inl_ne _ _ _ h]
  · cases b
    · rw [PermutationCycles.capPerm_false, inserted_face_false]
    · rw [PermutationCycles.capPerm_true, inserted_face_true]

/-- Inserting a cap into a nonempty boundary adds one face; all other face cycles correspond
bijectively to the old face cycles, including the face subdivided by the second cap end. -/
noncomputable def insertedFacesEquiv (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (hn : 0 < (before ++ after).length) :
    (BoundaryPairing.insert before after x sign old).ribbon.Face ≃ Option old.ribbon.Face :=
  (PermutationCycles.conjugateEquiv _ _ (insertEquiv before after x sign)
    (inserted_face_conjugacy before after x sign old hn)).symm.trans
      (PermutationCycles.capCyclesEquiv _ _)

/-- Actual face count under a noninitial cap insertion. -/
theorem card_insertedFaces (before after : List (SignedLetter X)) (x : X) (sign : Bool)
    (old : BoundaryPairing (before ++ after)) (hn : 0 < (before ++ after).length) :
    Fintype.card (BoundaryPairing.insert before after x sign old).ribbon.Face =
      Fintype.card old.ribbon.Face + 1 := by
  simpa using Fintype.card_congr (insertedFacesEquiv before after x sign old hn)

/-- The first cap has two one-corner faces: there is no old face to subdivide. -/
theorem initial_face_identity (x : X) (sign : Bool) (old : BoundaryPairing ([] :
    List (SignedLetter X))) :
    (BoundaryPairing.insert [] [] x sign old).ribbon.face = Equiv.refl _ := by
  apply Equiv.ext
  intro d
  obtain ⟨d, rfl⟩ := (insertEquiv [] [] x sign).surjective d
  rcases d with d | b
  · exact d.elim0
  · cases b
    · exact inserted_face_false [] [] x sign old
    · change (finRotate _).symm
        ((BoundaryPairing.insert [] [] x sign old).ribbon.edge _) = _
      rw [inserted_edge_true, insertEquiv_false, insertEquiv_true]
      apply Fin.ext
      rw [CapCoordinates.predecessor_val]
      simp

/-- The empty ribbon has no dart-defined faces; its ambient empty-disc region is not a cycle. -/
theorem card_empty_faces : Fintype.card (BoundaryPairing.empty (X := X)).ribbon.Face = 0 := by
  have : IsEmpty (BoundaryPairing.empty (X := X)).ribbon.Face :=
    ⟨fun q ↦ Quotient.inductionOn q (fun d ↦ d.elim0)⟩
  exact Fintype.card_eq_zero

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.BoundaryPairing
