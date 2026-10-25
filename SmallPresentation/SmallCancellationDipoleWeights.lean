module

public import SmallPresentation.SmallCancellationGeometrySprayEdgeWeights
public import SmallPresentation.BasedIdentityReduction

/-!
# Indexed dipoles have opposite quotient-weighted contributions

A dipole consists of an actual relator-ribbon edge whose endpoint occurrences have the same
indexed relator, opposite signs, and corresponding reverse cyclic positions. Those data imply
equality of the original conjugators in the relator quotient. In particular the two original
occurrences have opposite weights. Neither quotient-conjugator equality nor cancellation is
a field of the dipole datum; both are proved from the actual edge-path equation.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {X Q : Type} [Group Q] (q : FreeGroup X →* Q)

/-- The return-side prefix of a killed word equals the complementary forward prefix. -/
theorem inverse_prefix_quotient (w : List (SignedLetter X)) (hw : q (FreeGroup.mk w) = 1)
    (n : ℕ) : q (prefixValue (FreeGroup.invRev w) n) = q (prefixValue w (w.length - n)) := by
  have h := congrArg q (prefixValue_invRev w n)
  simpa only [map_mul, hw, one_mul] using h

namespace IdentityBoundary

open RelationCoordinates

variable {I J : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))
    (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)

/-- Actual opposite indexed row corners joined by an edge in the constructed relator ribbon. -/
structure IndexedDipole where
  first : Fin s.length
  second : Fin s.length
  firstCorner : Fin (orientedWord (rows s[first].1.2) s[first].2).length
  secondCorner : Fin (orientedWord (rows s[second].1.2) s[second].2).length
  same_label : s[first].1.2 = s[second].1.2
  opposite_sign : s[second].2 = !s[first].2
  reverse_positions : firstCorner.val + secondCorner.val + 1 = (rows s[first].1.2).length
  edge_eq : (relatorRibbon paths rows s h).edge (discAt rows s first firstCorner) =
    discAt rows s second secondCorner

namespace IndexedDipole

variable {paths rows s h} (D : IndexedDipole paths rows s h)

/-- The two indexed occurrences are distinct, even when the displayed relator labels repeat. -/
theorem first_ne_second : D.first ≠ D.second := by
  intro he
  have hs := D.opposite_sign
  rw [he] at hs
  cases s[D.second].2 <;> simp at hs

/-- The second signed row is the literal inverse word of the first. -/
theorem inverse_rows : orientedWord (rows s[D.second].1.2) s[D.second].2 =
    FreeGroup.invRev (orientedWord (rows s[D.first].1.2) s[D.first].2) := by
  rw [← D.same_label, D.opposite_sign, orientedWord_not]

/-- The actual band joining aligned inverse rows forces equality of the original quotient
conjugators, rather than merely equality of their relator labels. -/
theorem conjugator_eq (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1) :
    q s[D.first].1.1 = q s[D.second].1.1 := by
  have hp := relatorRibbon_edge_potential paths rows q hkill s h
    (discAt rows s D.first D.firstCorner)
  rw [D.edge_eq, discPotential_at paths rows q hkill, discPotential_at paths rows q hkill,
    discRead_at] at hp
  have hlen : (orientedWord (rows s[D.first].1.2) s[D.first].2).length - D.secondCorner.val =
      D.firstCorner.val + 1 := by
    have hr := D.reverse_positions
    have hl := orientedWord_length (rows s[D.first].1.2) s[D.first].2
    omega
  have hi := inverse_prefix_quotient q
    (orientedWord (rows s[D.first].1.2) s[D.first].2)
    (orientedWord_quotient rows q hkill _ _) D.secondCorner.val
  rw [hlen] at hi
  have hv := congrArg (fun w ↦ q (prefixValue w D.secondCorner.val)) D.inverse_rows
  rw [hv, hi] at hp
  have hs := congrArg q (prefixValue_succ
    (orientedWord (rows s[D.first].1.2) s[D.first].2) D.firstCorner)
  rw [map_mul] at hs
  rw [mul_assoc, ← hs] at hp
  exact (mul_right_cancel hp).symm

/-- The original second occurrence is based-matched to the inverse of the original first. -/
theorem matched_inverse (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1) (label : I → Option J) :
    Peiffer.Matched q label s[D.second] (Peiffer.inverse s[D.first]) := by
  refine ⟨D.same_label.symm, D.opposite_sign, fun _ ↦ ?_⟩
  exact (D.conjugator_eq q hkill).symm

/-- Removing the two indexed dipole occurrences removes zero total weighted contribution. -/
theorem weight_cancel (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1) (label : I → Option J) :
    Peiffer.weight q label s[D.first] + Peiffer.weight q label s[D.second] = 0 := by
  rw [Peiffer.weight_matched q label (D.matched_inverse q hkill label), Peiffer.weight_inverse]
  exact add_neg_cancel _

end IndexedDipole
end IdentityBoundary
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
