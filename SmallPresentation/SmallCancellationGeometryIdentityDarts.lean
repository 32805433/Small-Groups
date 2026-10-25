module

public import SmallPresentation.SmallCancellationGeometryIdentityCorridors

/-!
# Occurrence-indexed identity boundary incidence

A finite sum of typed block darts is identified bijectively with the literal expanded
boundary positions. Both cap pairing and corridor identification act on this same dart
set. Relator labels, orientations, and based paths remain accessible through the actual
occurrence index. Relator darts are precisely the fixed points of corridor identification.
This supplies concrete incidence data for the subsequent suppression of corridor interiors.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

/-- Boundary darts retain the exact occurrence, including repeated equal relators. -/
def Darts : Peiffer.Sequence (FreeGroup X) I → Type
  | [] => Fin 0
  | a :: s => BlockDart paths rows a ⊕ Darts s

instance dartsFintype (s : Peiffer.Sequence (FreeGroup X) I) : Fintype (Darts paths rows s) := by
  induction s with
  | nil => exact inferInstanceAs (Fintype (Fin 0))
  | cons a s ih =>
    let := ih
    exact inferInstanceAs (Fintype (BlockDart paths rows a ⊕ Darts paths rows s))

/-- Identify the entire typed incidence set with the original ordered boundary positions. -/
def dartCoordinates : (s : Peiffer.Sequence (FreeGroup X) I) →
    Darts paths rows s ≃ Fin (boundary paths rows s).length
  | [] => Equiv.refl _
  | a :: s => (Equiv.sumCongr (blockCoordinates paths rows a) (dartCoordinates s)).trans
      (appendCoordinates (block paths rows a) (boundary paths rows s))

/-- The index of the relator occurrence owning a boundary dart. -/
def occurrence : (s : Peiffer.Sequence (FreeGroup X) I) → Darts paths rows s → Fin s.length
  | [], d => Fin.elim0 d
  | _ :: _, .inl _ => 0
  | _ :: s, .inr d => (occurrence s d).succ

/-- Read the literal signed letter, preserving its position in its owning block. -/
def dartRead : (s : Peiffer.Sequence (FreeGroup X) I) → Darts paths rows s → SignedLetter X
  | [], d => Fin.elim0 d
  | a :: _, .inl d => blockRead paths rows a d
  | _ :: s, .inr d => dartRead s d

/-- Typed incidence readings agree with the ordered cut-open boundary, not merely its value. -/
theorem dartCoordinates_read (s : Peiffer.Sequence (FreeGroup X) I) (d : Darts paths rows s) :
    (boundary paths rows s)[dartCoordinates paths rows s d] = dartRead paths rows s d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · change (block paths rows a ++ boundary paths rows s)[appendCoordinates _ _ (.inl (blockCoordinates paths rows a d))] = _
      rw [appendCoordinates_left]
      exact blockCoordinates_read paths rows a d
    · change (block paths rows a ++ boundary paths rows s)[appendCoordinates _ _ (.inr (dartCoordinates paths rows s d))] = _
      rw [appendCoordinates_right]
      exact ih d

/-- Identify the two sides of every based corridor while retaining relator boundary darts. -/
def corridorIdentification : (s : Peiffer.Sequence (FreeGroup X) I) →
    Equiv.Perm (Darts paths rows s)
  | [] => Equiv.refl _
  | a :: s => Equiv.sumCongr (corridorReverse paths rows a) (corridorIdentification s)

theorem corridorIdentification_involutive (s : Peiffer.Sequence (FreeGroup X) I) :
    Function.Involutive (corridorIdentification paths rows s) := by
  intro d
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · exact congrArg Sum.inl (corridorReverse_involutive paths rows a d)
    · exact congrArg Sum.inr (ih d)

/-- A corridor never changes the occurrence to which one of its sides belongs. -/
theorem occurrence_corridorIdentification (s : Peiffer.Sequence (FreeGroup X) I)
    (d : Darts paths rows s) :
    occurrence paths rows s (corridorIdentification paths rows s d) =
      occurrence paths rows s d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · rfl
    · exact congrArg Fin.succ (ih d)

/-- Letters at paired corridor sides have opposite signs. -/
theorem corridorIdentification_read (s : Peiffer.Sequence (FreeGroup X) I)
    (d : Darts paths rows s) (hd : corridorIdentification paths rows s d ≠ d) :
    dartRead paths rows s (corridorIdentification paths rows s d) =
      reverseLetter (dartRead paths rows s d) := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · exact corridorReverse_read paths rows a d (fun he ↦ hd (congrArg Sum.inl he))
    · exact ih d (fun he ↦ hd (congrArg Sum.inr he))

/-- Distinct boundary positions on each labelled and oriented relator disc. -/
def DiscDarts : Peiffer.Sequence (FreeGroup X) I → Type
  | [] => Fin 0
  | a :: s => Fin (orientedWord (rows a.1.2) a.2).length ⊕ DiscDarts s

/-- Include the actual relator incidences among all boundary and corridor incidences. -/
def discInclusion : (s : Peiffer.Sequence (FreeGroup X) I) →
    DiscDarts rows s → Darts paths rows s
  | [], d => Fin.elim0 d
  | _ :: _, .inl d => .inl (.inr (.inl d))
  | _ :: s, .inr d => .inr (discInclusion s d)

theorem discInclusion_injective (s : Peiffer.Sequence (FreeGroup X) I) :
    Function.Injective (discInclusion paths rows s) := by
  intro d e he
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d <;> rcases e with e | e
    · exact congrArg Sum.inl (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj he)))
    · simp only [discInclusion] at he
      cases he
    · simp only [discInclusion] at he
      cases he
    · exact congrArg Sum.inr (ih (Sum.inr.inj he))

/-- Exactly the marked relator-boundary incidences remain unpaired by the corridors. -/
theorem corridorIdentification_fixed_iff (s : Peiffer.Sequence (FreeGroup X) I)
    (d : Darts paths rows s) :
    corridorIdentification paths rows s d = d ↔ ∃ e, discInclusion paths rows s e = d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · change Sum.inl (corridorReverse paths rows a d) = Sum.inl d ↔ _
      rw [Sum.inl.injEq, corridorReverse_fixed_iff]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨.inl k, rfl⟩
      · rintro ⟨k, hk⟩
        rcases k with k | k
        · exact ⟨k, (Sum.inl.inj hk).symm⟩
        · simp only [discInclusion] at hk
          cases hk
    · change Sum.inr (corridorIdentification paths rows s d) = Sum.inr d ↔ _
      rw [Sum.inr.injEq, ih]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨.inr k, rfl⟩
      · rintro ⟨k, hk⟩
        rcases k with k | k
        · simp only [discInclusion] at hk
          cases hk
        · exact ⟨k, Sum.inr.inj hk⟩

/-- The cap involution on these same typed incidences, obtained from free reduction. -/
noncomputable def capIdentification (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Equiv.Perm (Darts paths rows s) :=
  (dartCoordinates paths rows s).trans ((ribbon paths rows s h).edge.trans
    (dartCoordinates paths rows s).symm)

theorem capIdentification_involutive (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Function.Involutive (capIdentification paths rows s h) := by
  intro d
  apply (dartCoordinates paths rows s).injective
  simp only [capIdentification, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact (ribbon paths rows s h).edge_involutive _

theorem capIdentification_ne (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) (d : Darts paths rows s) :
    capIdentification paths rows s h d ≠ d := by
  intro he
  apply (ribbon paths rows s h).edge_ne (dartCoordinates paths rows s d)
  have hh := congrArg (dartCoordinates paths rows s) he
  simpa only [capIdentification, Equiv.trans_apply, Equiv.apply_symm_apply] using hh

theorem capIdentification_read (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) (d : Darts paths rows s) :
    dartRead paths rows s (capIdentification paths rows s h d) =
      reverseLetter (dartRead paths rows s d) := by
  rw [← dartCoordinates_read, ← dartCoordinates_read]
  simp only [capIdentification, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact ribbon_inverse_labels paths rows s h (dartCoordinates paths rows s d)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
