module

public import SmallPresentation.SmallCancellationGeometryIdentityBoundary

/-!
# Indexed corridor sides and disc incidences

The cut-open identity boundary is identified with typed darts: each dart belongs to a
specified occurrence and to its outward path, signed relator boundary, or return path.
The two sides of each corridor have an explicit orientation-reversing identification.
These coordinates retain disc labels and signs even when two evaluated relators coincide.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

/-- Boundary positions on the two corridor sides and on the signed relator disc. -/
abbrev BlockDart (a : Peiffer.Occurrence (FreeGroup X) I) :=
  Fin (paths.word a.1.1).length ⊕
    (Fin (orientedWord (rows a.1.2) a.2).length ⊕ Fin (paths.word a.1.1).length)

/-- Concatenation identifies a disjoint sum of literal word positions with their full word. -/
def appendCoordinates (u v : List (SignedLetter X)) :
    Fin u.length ⊕ Fin v.length ≃ Fin (u ++ v).length :=
  finSumFinEquiv.trans (finCongr (by simp))

@[simp] theorem appendCoordinates_left (u v : List (SignedLetter X)) (d : Fin u.length) :
    (u ++ v)[appendCoordinates u v (.inl d)] = u[d] := by
  simp [appendCoordinates, List.getElem_append_left]

@[simp] theorem appendCoordinates_right (u v : List (SignedLetter X)) (d : Fin v.length) :
    (u ++ v)[appendCoordinates u v (.inr d)] = v[d] := by
  simp [appendCoordinates, List.getElem_append_right]

/-- Typed block darts correspond bijectively to the literal block boundary positions. -/
def blockCoordinates (a : Peiffer.Occurrence (FreeGroup X) I) :
    BlockDart paths rows a ≃ Fin (block paths rows a).length :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _)
    (finCongr FreeGroup.invRev_length.symm))).trans
    ((Equiv.sumCongr (Equiv.refl _) (appendCoordinates _ _)).trans
      ((appendCoordinates _ _).trans (finCongr (by simp [block, List.length_append]))))

/-- Read the signed letter at a typed block dart. -/
def blockRead (a : Peiffer.Occurrence (FreeGroup X) I) :
    BlockDart paths rows a → SignedLetter X
  | .inl d => (paths.word a.1.1)[d]
  | .inr (.inl d) => (orientedWord (rows a.1.2) a.2)[d]
  | .inr (.inr d) => (FreeGroup.invRev (paths.word a.1.1))[Fin.cast
      FreeGroup.invRev_length.symm d]

/-- The typed reading agrees with the actual cut-open boundary. -/
theorem blockCoordinates_read (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : BlockDart paths rows a) :
    (block paths rows a)[blockCoordinates paths rows a d] = blockRead paths rows a d := by
  have hlen : (block paths rows a).length = (paths.word a.1.1).length +
      (orientedWord (rows a.1.2) a.2).length + (paths.word a.1.1).length := by
    simp [block, Nat.add_assoc]
  rcases d with d | (d | d)
  · have hd := d.isLt
    change (block paths rows a)[d.val] = (paths.word a.1.1)[d.val]
    simp [block, d.isLt]
  · have hd' := d.isLt
    change (block paths rows a)[(paths.word a.1.1).length + d.val] =
      (orientedWord (rows a.1.2) a.2)[d.val]
    have hd : d.val < (rows a.1.2).length := by simpa using d.isLt
    simp [block, hd]
  · have hd' := d.isLt
    change (block paths rows a)[(paths.word a.1.1).length +
        ((orientedWord (rows a.1.2) a.2).length + d.val)] =
      (FreeGroup.invRev (paths.word a.1.1))[d.val]
    simp [block]

/-- Pair opposite corridor sides in their reverse linear order, fixing relator darts. -/
def corridorReverse (a : Peiffer.Occurrence (FreeGroup X) I) : Equiv.Perm (BlockDart paths rows a) where
  toFun
    | .inl d => .inr (.inr d.rev)
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr d) => .inl d.rev
  invFun
    | .inl d => .inr (.inr d.rev)
    | .inr (.inl d) => .inr (.inl d)
    | .inr (.inr d) => .inl d.rev
  left_inv d := by rcases d with d | (d | d) <;> simp
  right_inv d := by rcases d with d | (d | d) <;> simp

theorem corridorReverse_involutive (a : Peiffer.Occurrence (FreeGroup X) I) :
    Function.Involutive (corridorReverse paths rows a) := by
  intro d
  rcases d with d | (d | d) <;> simp [corridorReverse]

/-- A dart is fixed precisely when it is an incidence on the marked relator disc. -/
theorem corridorReverse_fixed_iff (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : BlockDart paths rows a) :
    corridorReverse paths rows a d = d ↔ ∃ k, d = .inr (.inl k) := by
  rcases d with d | (d | d) <;> simp [corridorReverse]

/-- Reading the return side in reverse order changes the sign of its letter. -/
theorem invRev_letter (w : List (SignedLetter X)) (d : Fin w.length) :
    (FreeGroup.invRev w)[Fin.cast FreeGroup.invRev_length.symm d.rev] = reverseLetter w[d] := by
  simp only [Fin.getElem_fin, FreeGroup.invRev, List.getElem_reverse, List.length_map, List.getElem_map]
  change reverseLetter (w[w.length - 1 - (w.length - (d.val + 1))]) = reverseLetter w[d.val]
  congr 2
  omega

/-- Every corridor identification pairs inverse generator letters. -/
theorem corridorReverse_read (a : Peiffer.Occurrence (FreeGroup X) I)
    (d : BlockDart paths rows a) (hd : corridorReverse paths rows a d ≠ d) :
    blockRead paths rows a (corridorReverse paths rows a d) =
      reverseLetter (blockRead paths rows a d) := by
  rcases d with d | (d | d)
  · exact invRev_letter _ _
  · exact (hd rfl).elim
  · change (paths.word a.1.1)[d.rev] =
      reverseLetter ((FreeGroup.invRev (paths.word a.1.1))[Fin.cast
        FreeGroup.invRev_length.symm d])
    have h := invRev_letter (paths.word a.1.1) d.rev
    simpa only [Fin.rev_rev, reverseLetter_reverseLetter] using
      (congrArg reverseLetter h).symm

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
