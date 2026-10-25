module

public import SmallPresentation.WeightedIdentitySequences

/-! Functoriality of quotient-weighted identities under group homomorphisms. -/
@[expose] public section

namespace SmallPresentationStatements.RelationCoordinates.Weighted

variable {F Q Q' I J : Type} [Group F] [Group Q] [Group Q']

/-- Apply a homomorphism to the quotient coordinate of each basis element. -/
def mapCoordinates (f : Q →* Q') : Coordinates (Q := Q) (J := J) →+
    Coordinates (Q := Q') (J := J) :=
  FreeAbelianGroup.map (fun x ↦ (f x.1, x.2))

@[simp] theorem mapCoordinates_generator (f : Q →* Q') (label : I → Option J)
    (q : Q) (i : I) :
    mapCoordinates f (generator label q i) = generator label (f q) i := by
  cases h : label i <;> simp [generator, h, mapCoordinates]

/-- Weighted vectors commute with changing their target quotient. -/
theorem mapCoordinates_vector (p : F →* Q) (f : Q →* Q') (label : I → Option J) :
    (mapCoordinates (J := J) f).toMultiplicative.comp (vector p label) =
      vector (f.comp p) label := by
  apply FreeGroup.ext_hom
  rintro ⟨g, i⟩
  simp [vector]

/-- Weighted identity balance is preserved by every homomorphism of target groups. -/
theorem balanced_map (rel : I → F) (p : F →* Q) (f : Q →* Q')
    (label : I → Option J) (h : Balanced rel p label) :
    Balanced rel (f.comp p) label := by
  intro w hw
  change vector (f.comp p) label w = 1
  rw [← mapCoordinates_vector, MonoidHom.comp_apply, h hw, map_one]

/-- Changing the quotient by an isomorphism preserves the exact weighted condition. -/
theorem balanced_equiv_iff (rel : I → F) (p : F →* Q) (e : Q ≃* Q')
    (label : I → Option J) :
    Balanced rel (e.toMonoidHom.comp p) label ↔ Balanced rel p label := by
  constructor
  · intro h
    have hh := balanced_map rel (e.toMonoidHom.comp p) e.symm.toMonoidHom label h
    have he : e.symm.toMonoidHom.comp (e.toMonoidHom.comp p) = p := by
      ext x
      exact e.symm_apply_apply _
    rwa [he] at hh
  · exact balanced_map rel p e.toMonoidHom label

end SmallPresentationStatements.RelationCoordinates.Weighted
