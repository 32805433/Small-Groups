module

public import SmallPresentation.SmallCancellationGeometrySprayCorridors

/-!
# Actual relator-ribbon edge equations for based paths

The prefix potential on the expanded identity boundary descends through the actual finite
alternating bands. This proves an explicit quotient equation between the marked corner paths
at every edge of the constructed relator ribbon. No arbitrary change-of-spray equivalence,
planarity, or inverse-conjugate equation is supplied as an assumption.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I Q : Type} [Group Q] (paths : WordSection X)
    (rows : I → List (SignedLetter X)) (q : FreeGroup X →* Q)

/-- Value of the actual boundary prefix at a typed identity-boundary dart. -/
def dartPotential (s : Peiffer.Sequence (FreeGroup X) I) (d : Darts paths rows s) : Q :=
  q (prefixValue (boundary paths rows s) (dartCoordinates paths rows s d).val)

theorem dartPotential_head (a : Peiffer.Occurrence (FreeGroup X) I)
    (s : Peiffer.Sequence (FreeGroup X) I) (d : BlockDart paths rows a) :
    dartPotential paths rows q (a :: s) (.inl d) = blockPotential paths rows q a d := by
  change q (prefixValue (block paths rows a ++ boundary paths rows s)
    (blockCoordinates paths rows a d).val) = _
  rw [prefixValue_append_left _ _ _ (Nat.le_of_lt (blockCoordinates paths rows a d).isLt)]
  rfl

variable (hkill : ∀ i, q (FreeGroup.mk (rows i)) = 1)
include hkill

theorem dartPotential_tail (a : Peiffer.Occurrence (FreeGroup X) I)
    (s : Peiffer.Sequence (FreeGroup X) I) (d : Darts paths rows s) :
    dartPotential paths rows q (a :: s) (.inr d) = dartPotential paths rows q s d := by
  change q (prefixValue (block paths rows a ++ boundary paths rows s)
    ((block paths rows a).length + (dartCoordinates paths rows s d).val)) = _
  rw [prefixValue_append_right, map_mul, block_quotient paths rows q hkill, one_mul]
  rfl

/-- Every non-fixed corridor step obeys the actual global-prefix potential law. -/
theorem corridorIdentification_potential (s : Peiffer.Sequence (FreeGroup X) I)
    (d : Darts paths rows s) (hd : corridorIdentification paths rows s d ≠ d) :
    dartPotential paths rows q s (corridorIdentification paths rows s d) =
      dartPotential paths rows q s d * q (letterValue (dartRead paths rows s d)) := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · change dartPotential paths rows q (a :: s) (.inl (corridorReverse paths rows a d)) = _
      rw [dartPotential_head, dartPotential_head]
      exact corridorReverse_potential paths rows q hkill a d
        (fun h ↦ hd (congrArg Sum.inl h))
    · change dartPotential paths rows q (a :: s) (.inr (corridorIdentification paths rows s d)) = _
      rw [dartPotential_tail paths rows q hkill, dartPotential_tail paths rows q hkill]
      exact ih d (fun h ↦ hd (congrArg Sum.inr h))

omit hkill in
/-- The cap equation holds already in the free group and hence in every quotient. -/
theorem capIdentification_potential (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)
    (d : Darts paths rows s) :
    dartPotential paths rows q s (capIdentification paths rows s h d) =
      dartPotential paths rows q s d * q (letterValue (dartRead paths rows s d)) := by
  have hh := congrArg q ((pairing paths rows s h).edge_prefix (dartCoordinates paths rows s d))
  simpa only [dartPotential, capIdentification, Equiv.trans_apply, Equiv.apply_symm_apply,
    map_mul, dartCoordinates_read, ribbon] using hh

/-- The path potential restricted to actual retained relator-disc corners. -/
def discPotential (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) : Q :=
  dartPotential paths rows q s (discInclusion paths rows s d)

/-- An actual suppressed edge gives the expected equation between its two corner paths. -/
theorem relatorRibbon_edge_potential (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) (d : DiscDarts rows s) :
    discPotential paths rows q s ((relatorRibbon paths rows s h).edge d) =
      discPotential paths rows q s d * q (letterValue (discRead paths rows s d)) := by
  let B := bands paths rows s h
  have hp := B.endpoint_potential (fun x ↦ q (letterValue x))
    (fun x ↦ by rw [letterValue_reverse, map_inv]) (dartPotential paths rows q s)
    (capIdentification_potential paths rows q s h)
    (corridorIdentification_potential paths rows q hkill s)
    (discEndpointEquiv paths rows s h d)
  have hv (e : B.Endpoint) :
      discInclusion paths rows s ((discEndpointEquiv paths rows s h).symm e) = e.val :=
    congrArg Subtype.val ((discEndpointEquiv paths rows s h).apply_symm_apply e)
  change dartPotential paths rows q s (discInclusion paths rows s
    ((discEndpointEquiv paths rows s h).symm
      (B.endpoint (discEndpointEquiv paths rows s h d)))) = _
  rw [hv]
  exact hp

/-- The restricted potential is the quotient value of the previously constructed corner path. -/
theorem discPotential_at (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    discPotential paths rows q s (discAt rows s i d) =
      q s[i].1.1 * q (prefixValue (orientedWord (rows s[i].1.2) s[i].2) d.val) := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    induction i using Fin.cases with
    | zero =>
      change dartPotential paths rows q (a :: s) (.inl (.inr (.inl d))) = _
      rw [dartPotential_head]
      exact blockPotential_row paths rows q a d
    | succ i =>
      change dartPotential paths rows q (a :: s) (.inr (discInclusion paths rows s
        (discAt rows s i d))) = _
      rw [dartPotential_tail paths rows q hkill]
      exact ih i d

theorem discPotential_eq_cornerPath (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    discPotential paths rows q s (discAt rows s i d) =
      q (FreeGroup.mk (cornerPath paths rows s i d.val)) := by
  rw [discPotential_at paths rows q hkill, cornerPath_quotient paths rows q hkill]
  rfl

/-- An edge between specified original indexed corners has an explicit quotient path equation. -/
theorem edge_cornerPath (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1)
    (i j : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length)
    (e : Fin (orientedWord (rows s[j].1.2) s[j].2).length)
    (hedge : (relatorRibbon paths rows s h).edge (discAt rows s i d) = discAt rows s j e) :
    q (FreeGroup.mk (cornerPath paths rows s j e.val)) =
      q (FreeGroup.mk (cornerPath paths rows s i d.val)) *
        q (letterValue (orientedWord (rows s[i].1.2) s[i].2)[d]) := by
  have hp := relatorRibbon_edge_potential paths rows q hkill s h (discAt rows s i d)
  rw [hedge, discPotential_eq_cornerPath paths rows q hkill,
    discPotential_eq_cornerPath paths rows q hkill, discRead_at] at hp
  exact hp

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
