module

public import SmallPresentation.PeifferIdentities
public import SmallPresentation.SmallCancellationGeometryPairingRibbon

/-!
# The actual cut-open boundary of a labelled identity sequence

Every indexed occurrence retains its relator label, sign, and conjugating path. We expand
it as the path, the chosen relator word in the specified orientation, and the reverse path.
The resulting literal word evaluates to the original Peiffer product. Thus an evaluated
identity supplies an actual noncrossing inverse-letter pairing and a labelled boundary
ribbon. This is the boundary-folding part of realization; attaching relator discs and
recovering their spray after folding are separate geometric steps.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type}

/-- A specified spelling of every group element, with its evaluation law. -/
structure WordSection (X : Type) where
  word : FreeGroup X → List (SignedLetter X)
  evaluates : ∀ g, FreeGroup.mk (word g) = g

/-- Word choices exist without a decidable equality or finite generation assumption. -/
noncomputable def chosenSection (X : Type) : WordSection X where
  word := Quot.out
  evaluates := Quot.out_eq

/-- Reverse a displayed row exactly when its occurrence has negative orientation. -/
def orientedWord (w : List (SignedLetter X)) (sign : Bool) : List (SignedLetter X) :=
  bif sign then w else FreeGroup.invRev w

@[simp] theorem orientedWord_length (w : List (SignedLetter X)) (sign : Bool) :
    (orientedWord w sign).length = w.length := by cases sign <;> simp [orientedWord]

@[simp] theorem orientedWord_not (w : List (SignedLetter X)) (sign : Bool) :
    orientedWord w (!sign) = FreeGroup.invRev (orientedWord w sign) := by
  cases sign <;> simp [orientedWord]

variable (paths : WordSection X) (rows : I → List (SignedLetter X))

/-- The literal based boundary around a single indexed relator disc. -/
def block (a : Peiffer.Occurrence (FreeGroup X) I) : List (SignedLetter X) :=
  paths.word a.1.1 ++ orientedWord (rows a.1.2) a.2 ++ FreeGroup.invRev (paths.word a.1.1)

/-- The cut-open boundary retains the original order of the based relator discs. -/
def boundary (s : Peiffer.Sequence (FreeGroup X) I) : List (SignedLetter X) :=
  s.flatMap (block paths rows)

@[simp] theorem boundary_nil : boundary paths rows [] = [] := rfl

@[simp] theorem boundary_cons (a : Peiffer.Occurrence (FreeGroup X) I)
    (s : Peiffer.Sequence (FreeGroup X) I) :
    boundary paths rows (a :: s) = block paths rows a ++ boundary paths rows s := rfl

@[simp] theorem boundary_append (s t : Peiffer.Sequence (FreeGroup X) I) :
    boundary paths rows (s ++ t) = boundary paths rows s ++ boundary paths rows t := by
  simp [boundary]

/-- The block evaluates to exactly the signed conjugate recorded in the sequence. -/
theorem block_evaluates (a : Peiffer.Occurrence (FreeGroup X) I) :
    FreeGroup.mk (block paths rows a) = Peiffer.term (fun i ↦ FreeGroup.mk (rows i)) a := by
  rcases a with ⟨⟨w, i⟩, sign⟩
  cases sign <;>
    simp only [block, orientedWord, Bool.cond_false,
      Bool.cond_true, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, paths.evaluates, Peiffer.term]
  group

/-- No passage to a presented quotient occurs: equality is in the original free group. -/
theorem boundary_evaluates (s : Peiffer.Sequence (FreeGroup X) I) :
    FreeGroup.mk (boundary paths rows s) =
      Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rw [boundary_cons, ← FreeGroup.mul_mk, block_evaluates, ih]
    rfl

/-- Every evaluated identity gives a cap-insertion certificate on its actual expanded word. -/
noncomputable def pairing (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    BoundaryPairing (boundary paths rows s) :=
  BoundaryPairing.ofMkEqOne _ ((boundary_evaluates paths rows s).trans h)

/-- The freely trivial expanded boundary, with its actual inverse-labelled ribbon edges. -/
noncomputable def ribbon (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    RibbonMap (Fin (boundary paths rows s).length) := (pairing paths rows s h).ribbon

/-- The labels of paired boundary positions are inverse letters. -/
theorem ribbon_inverse_labels (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)
    (d : Fin (boundary paths rows s).length) :
    (boundary paths rows s)[(ribbon paths rows s h).edge d] =
      reverseLetter ((boundary paths rows s)[d]) :=
  (pairing paths rows s h).ribbon_edge_letter d

/-- The constructed pairing is noncrossing in the actual cut-open boundary order. -/
theorem ribbon_noncrossing (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)
    (d e : Fin (boundary paths rows s).length)
    (hd : d.val < ((ribbon paths rows s h).edge d).val)
    (he : e.val < ((ribbon paths rows s h).edge e).val) :
    ¬(d.val < e.val ∧ e.val < ((ribbon paths rows s h).edge d).val ∧
      ((ribbon paths rows s h).edge d).val < ((ribbon paths rows s h).edge e).val) :=
  (pairing paths rows s h).ribbon_noncrossing d e hd he

/-- Any specified family of group-valued relators can be realized by the chosen spellings. -/
noncomputable def pairingOfIdentity (rel : I → FreeGroup X)
    (s : Peiffer.Sequence (FreeGroup X) I) (h : Peiffer.evaluation rel s = 1) :
    BoundaryPairing (boundary paths (fun i ↦ paths.word (rel i)) s) :=
  pairing paths (fun i ↦ paths.word (rel i)) s (by simpa only [paths.evaluates] using h)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
