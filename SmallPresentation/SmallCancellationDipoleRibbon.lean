module

public import SmallPresentation.SmallCancellationDipoleCoordinates
public import SmallPresentation.SmallCancellationDipoleWeights

/-!
# Based ribbons with arbitrary indexed row words

This representation retains the individual occurrence index, the complete signed row word,
and its quotient basepoint. The edge-potential law is local path data; it does not assume
planarity, a dipole, or any small-cancellation conclusion. It is proved for the actual
identity-sequence ribbon by the preceding modules.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {O X Q : Type} [Group Q]

abbrev RowDarts (words : O → List (SignedLetter X)) := Σ o, Fin (words o).length

def rowRotation (words : O → List (SignedLetter X)) : Equiv.Perm (RowDarts words) :=
  Equiv.sigmaCongrRight (fun o ↦ finRotate (words o).length)

def rowRead (words : O → List (SignedLetter X)) (d : RowDarts words) : SignedLetter X :=
  (words d.1)[d.2]

def rowPotential (words : O → List (SignedLetter X)) (q : FreeGroup X →* Q) (base : O → Q)
    (d : RowDarts words) : Q := base d.1 * q (prefixValue (words d.1) d.2.val)

/-- An actual row ribbon with local quotient path data. -/
structure BasedRowRibbon (words : O → List (SignedLetter X)) (q : FreeGroup X →* Q) where
  map : RibbonMap (RowDarts words)
  rotation_eq : map.rotation = rowRotation words
  base : O → Q
  row_killed : ∀ o, q (FreeGroup.mk (words o)) = 1
  edge_letters : ∀ d, rowRead words (map.edge d) = reverseLetter (rowRead words d)
  edge_paths : ∀ d, rowPotential words q base (map.edge d) =
    rowPotential words q base d * q (letterValue (rowRead words d))

namespace BasedRowRibbon

variable {words : O → List (SignedLetter X)} {q : FreeGroup X →* Q}
    (P : BasedRowRibbon words q)

/-- Reverse cyclic positions in a literal inverse row. -/
def inverseCorner {i j : O} (hword : words j = FreeGroup.invRev (words i)) :
    Fin (words i).length ≃ Fin (words j).length :=
  let reverse : Equiv.Perm (Fin (words i).length) :=
    ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  reverse.trans (finCongr (by rw [hword, FreeGroup.invRev_length]))

@[simp] theorem inverseCorner_val {i j : O}
    (hword : words j = FreeGroup.invRev (words i)) (d : Fin (words i).length) :
    (inverseCorner hword d).val = (words i).length - (d.val + 1) := rfl

theorem inverseCorner_letter {i j : O} (hword : words j = FreeGroup.invRev (words i))
    (d : Fin (words i).length) :
    (words j)[inverseCorner hword d] = reverseLetter (words i)[d] := by
  have h := IdentityBoundary.invRev_letter (words i) d
  simpa only [Fin.getElem_fin, inverseCorner_val, hword, Fin.val_cast, Fin.val_rev] using h

/-- Opposite rows joined at corresponding corners give an actual dipole anchor. -/
structure Dipole where
  first : O
  second : O
  distinct : first ≠ second
  inverse_words : words second = FreeGroup.invRev (words first)
  anchor : Fin (words first).length
  edge_anchor : P.map.edge ⟨first, anchor⟩ =
    ⟨second, inverseCorner inverse_words anchor⟩

namespace Dipole

variable {P} (D : P.Dipole)

/-- Quotient basepoints agree as a consequence of the actual anchor edge equation. -/
theorem base_eq : P.base D.first = P.base D.second := by
  have hp := P.edge_paths ⟨D.first, D.anchor⟩
  rw [D.edge_anchor] at hp
  change P.base D.second * q (prefixValue (words D.second)
    (inverseCorner D.inverse_words D.anchor).val) =
      P.base D.first * q (prefixValue (words D.first) D.anchor.val) *
        q (letterValue (words D.first)[D.anchor]) at hp
  have hv := congrArg (fun w ↦ q (prefixValue w
    (inverseCorner D.inverse_words D.anchor).val)) D.inverse_words
  rw [hv, inverse_prefix_quotient q _ (P.row_killed D.first), inverseCorner_val] at hp
  have hn : (words D.first).length - ((words D.first).length - (D.anchor.val + 1)) =
      D.anchor.val + 1 := by omega
  rw [hn] at hp
  have hs := congrArg q (prefixValue_succ (words D.first) D.anchor)
  rw [map_mul] at hs
  rw [mul_assoc, ← hs] at hp
  exact (mul_right_cancel hp).symm

/-- Once an anchor is fixed, every corresponding corner pair has the corridor potential law. -/
theorem inverse_corner_potential (d : Fin (words D.first).length) :
    rowPotential words q P.base ⟨D.second, inverseCorner D.inverse_words d⟩ =
      rowPotential words q P.base ⟨D.first, d⟩ * q (letterValue (words D.first)[d]) := by
  change P.base D.second * q (prefixValue (words D.second)
    (inverseCorner D.inverse_words d).val) = _
  have hv := congrArg (fun w ↦ q (prefixValue w
    (inverseCorner D.inverse_words d).val)) D.inverse_words
  rw [hv, inverse_prefix_quotient q _ (P.row_killed D.first), inverseCorner_val]
  have hn : (words D.first).length - ((words D.first).length - (d.val + 1)) = d.val + 1 := by
    omega
  rw [hn, prefixValue_succ, map_mul, ← D.base_eq]
  exact (mul_assoc _ _ _).symm

end Dipole
end BasedRowRibbon
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
