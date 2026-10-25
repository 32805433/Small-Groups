module

public import SmallPresentation.SmallCancellationGeometryCanonicalWords
public import SmallPresentation.SmallCancellationGeometryAugmentedFactor
public import SmallPresentation.SmallCancellationGeometryIdentityVertexWords

/-! Every actual old canonical relator occurrence supplies the proved factor-disc invariants. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords

open RelationCoordinates RelationDerivative.CanonicalSchur IdentityBoundary Homology

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) (rows : ∀ i, Fin (length i) → Syllable G)

theorem oriented_oldWord_tag (r : OldIndex G) (sign : Bool)
    (x : SignedLetter (Syllable G)) (hx : x ∈ orientedWord (oldWord G r) sign) :
    x.1.1 = r.1 := by
  cases sign
  · simp only [orientedWord, Bool.cond_false, FreeGroup.invRev, List.mem_reverse,
      List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact oldWord_tag G r y hy
  · exact oldWord_tag G r x hx

theorem oriented_oldWord_product (r : OldIndex G) (sign : Bool) :
    ((orientedWord (oldWord G r) sign).map (coefficient G)).prod = 1 := by
  cases sign
  · rw [coefficient_product]
    change FreeProductPresentation.projection G (FreeGroup.mk (FreeGroup.invRev (oldWord G r))) = 1
    rw [← FreeGroup.inv_mk, map_inv]
    have hh := oldWord_product G r
    rw [coefficient_product] at hh
    rw [hh, inv_one]
  · exact oldWord_product G r

variable (paths : WordSection (Syllable G))
    (s : Peiffer.Sequence (FreeGroup (Syllable G)) (OldIndex G ⊕ I))
    (hs : Peiffer.evaluation (all G (rowLift G length rows)) s = 1)

/-- An actual old occurrence in the initial identity ribbon is a normalizable factor disc. -/
theorem old_occurrence_factorDisc (i : Fin s.length) (r : OldIndex G)
    (hi : s[i].1.2 = Sum.inl r)
    (hp : 0 < (orientedWord (words G length rows s[i].1.2) s[i].2).length) :
    FactorDisc (augmentedData G length rows paths s hs).labelling
      (discAt (words G length rows) s i ⟨0, hp⟩, false) := by
  let W := words G length rows
  let a := discAt W s i ⟨0, hp⟩
  let P := ordinary G length rows paths s hs
  let L := augmentedData G length rows paths s hs
  have tag_at (d : DiscDarts W s) (hd : discOccurrence W s d = i) :
      L.tag d = r.1 := by
    have hm := discRead_mem_oriented paths W s i d hd
    change discRead paths W s d ∈ orientedWord (words G length rows s[i].1.2) s[i].2 at hm
    rw [hi] at hm
    exact oriented_oldWord_tag G r s[i].2 _ hm
  apply L.factorDisc a
  · intro d hd
    have ho : discOccurrence W s d = i := by
      have hh := (disc_sameCycle_iff W s a d).mp hd
      rw [discOccurrence_at] at hh
      exact hh.symm
    exact (tag_at d ho).trans (tag_at a (discOccurrence_at W s i _)).symm
  · have hh := congrArg (fun l : List (SignedLetter (Syllable G)) ↦
        (l.map (coefficient G)).prod)
      (vertex_read_at_zero paths W s (identity_evaluates G length rows s hs) i hp)
    simp only [List.map_map, Function.comp_def] at hh
    change ((P.vertexBoundary a).map L.coefficient).prod = _ at hh
    rw [hh]
    change ((orientedWord (words G length rows s[i].1.2) s[i].2).map (coefficient G)).prod = 1
    rw [hi]
    exact oriented_oldWord_product G r s[i].2

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.CanonicalWords
