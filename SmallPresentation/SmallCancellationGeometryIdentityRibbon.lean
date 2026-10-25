module

public import SmallPresentation.SmallCancellationGeometryIdentityBands

/-!
# A labelled relator ribbon constructed from an actual Peiffer identity

The freely trivial expanded boundary supplies cap arcs. The typed corridor identifications
are suppressed by their actual finite alternating paths, producing inverse-labelled arcs
between the original relator-disc incidences. The vertex rotation is the prescribed cyclic
order on each signed row. The construction retains the original occurrence set, including
its relator labels, signs and based paths. Empty rows have no darts but their occurrence
indices are retained separately. Planarity and spray equivalence after suppression remain
separate obligations; this module makes no spherical Euler-characteristic assertion.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary

open RelationCoordinates

variable {X I : Type} (paths : WordSection X) (rows : I → List (SignedLetter X))

/-- Concrete band data from free reduction and the actual indexed corridor sides. -/
noncomputable def bands (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    BandSystem (Darts paths rows s) X where
  cap := capIdentification paths rows s h
  corridor := corridorIdentification paths rows s
  cap_involutive := capIdentification_involutive paths rows s h
  corridor_involutive := corridorIdentification_involutive paths rows s
  letter := dartRead paths rows s
  cap_letter := capIdentification_read paths rows s h
  corridor_letter := corridorIdentification_read paths rows s

/-- Include exactly the relator-disc incidences as endpoints of the alternating bands. -/
def discToEndpoint (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    DiscDarts rows s → (bands paths rows s h).Endpoint := fun d ↦
  ⟨discInclusion paths rows s d,
    (corridorIdentification_fixed_iff paths rows s _).mpr ⟨d, rfl⟩⟩

/-- No endpoint is introduced or lost during corridor suppression. -/
theorem discToEndpoint_bijective (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    Function.Bijective (discToEndpoint paths rows s h) := by
  constructor
  · intro d e he
    exact discInclusion_injective paths rows s (congrArg Subtype.val he)
  · intro d
    obtain ⟨e, he⟩ := (corridorIdentification_fixed_iff paths rows s d.val).mp d.property
    exact ⟨e, Subtype.ext he⟩

/-- Identify the resulting arc endpoints with the original labelled disc incidences. -/
noncomputable def discEndpointEquiv (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    DiscDarts rows s ≃ (bands paths rows s h).Endpoint :=
  Equiv.ofBijective _ (discToEndpoint_bijective paths rows s h)

/-- The prescribed positive cyclic order around each signed relator row. -/
def discRotation : (s : Peiffer.Sequence (FreeGroup X) I) → Equiv.Perm (DiscDarts rows s)
  | [] => Equiv.refl _
  | a :: s => Equiv.sumCongr (finRotate (orientedWord (rows a.1.2) a.2).length) (discRotation s)

/-- The actual occurrence index of a relator-disc dart. -/
def discOccurrence : (s : Peiffer.Sequence (FreeGroup X) I) → DiscDarts rows s → Fin s.length
  | [], d => Fin.elim0 d
  | _ :: _, .inl _ => 0
  | _ :: s, .inr d => (discOccurrence s d).succ

/-- The cyclic rotation stays on the same original relator occurrence. -/
theorem discOccurrence_rotation (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) :
    discOccurrence rows s (discRotation rows s d) = discOccurrence rows s d := by
  induction s with
  | nil => exact Fin.elim0 d
  | cons a s ih =>
    rcases d with d | d
    · rfl
    · exact congrArg Fin.succ (ih d)

/-- A typed local corner on a prescribed indexed disc gives its actual dart. -/
def discAt : (s : Peiffer.Sequence (FreeGroup X) I) →
    (i : Fin s.length) → Fin (orientedWord (rows s[i].1.2) s[i].2).length → DiscDarts rows s
  | [], i, _ => Fin.elim0 i
  | _ :: s, i, d => Fin.cases (fun d ↦ Sum.inl d)
      (fun j d ↦ Sum.inr (discAt s j d)) i d

theorem discOccurrence_at (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    discOccurrence rows s (discAt rows s i d) = i := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact congrArg Fin.succ (ih i d)

/-- The prescribed rotation is exactly the successor of the local relator corner. -/
theorem discRotation_at (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    discRotation rows s (discAt rows s i d) =
      discAt rows s i (finRotate (orientedWord (rows s[i].1.2) s[i].2).length d) := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact congrArg Sum.inr (ih i d)

/-- Read the original signed relator letter at a retained incidence. -/
def discRead (s : Peiffer.Sequence (FreeGroup X) I) (d : DiscDarts rows s) : SignedLetter X :=
  dartRead paths rows s (discInclusion paths rows s d)

theorem discRead_at (s : Peiffer.Sequence (FreeGroup X) I) (i : Fin s.length)
    (d : Fin (orientedWord (rows s[i].1.2) s[i].2).length) :
    discRead paths rows s (discAt rows s i d) = (orientedWord (rows s[i].1.2) s[i].2)[d] := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact ih i d

/-- The concrete relator ribbon: suppressed bands are its edges and row cycles its vertices. -/
noncomputable def relatorRibbon (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    RibbonMap (DiscDarts rows s) where
  edge := (discEndpointEquiv paths rows s h).trans
    ((bands paths rows s h).endpointPairing.trans (discEndpointEquiv paths rows s h).symm)
  edge_involutive d := by
    apply (discEndpointEquiv paths rows s h).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    exact (bands paths rows s h).endpoint_involutive _
  edge_ne d he := by
    apply (bands paths rows s h).endpoint_ne (discEndpointEquiv paths rows s h d)
    change (discEndpointEquiv paths rows s h).symm
      ((bands paths rows s h).endpoint (discEndpointEquiv paths rows s h d)) = d at he
    have he' := congrArg (discEndpointEquiv paths rows s h) he
    rw [Equiv.apply_symm_apply] at he'
    exact he'

  rotation := discRotation rows s

/-- The actual suppressed arc endpoints carry inverse generator letters. -/
theorem relatorRibbon_edge_read (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) (d : DiscDarts rows s) :
    discRead paths rows s ((relatorRibbon paths rows s h).edge d) =
      reverseLetter (discRead paths rows s d) := by
  have he := (bands paths rows s h).endpoint_letter (discEndpointEquiv paths rows s h d)
  have hv (e : (bands paths rows s h).Endpoint) :
      discInclusion paths rows s ((discEndpointEquiv paths rows s h).symm e) = e.val := by
    exact congrArg Subtype.val ((discEndpointEquiv paths rows s h).apply_symm_apply e)
  change dartRead paths rows s (discInclusion paths rows s
    ((discEndpointEquiv paths rows s h).symm
      ((bands paths rows s h).endpoint (discEndpointEquiv paths rows s h d)))) = _
  rw [hv]
  exact he

/-- An ordinary arc labelling of the resulting relator ribbon, with trivial coefficients. -/
noncomputable def relatorLabelling (s : Peiffer.Sequence (FreeGroup X) I)
    (h : Peiffer.evaluation (fun i ↦ FreeGroup.mk (rows i)) s = 1) :
    RibbonLabelling (relatorRibbon paths rows s h) X PUnit where
  arc := discRead paths rows s
  corner _ := PUnit.unit
  edge_arc := relatorRibbon_edge_read paths rows s h

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.IdentityBoundary
