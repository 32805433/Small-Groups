module

public import SmallPresentation.SmallCancellationGeometryFaceCapProducts
public import SmallPresentation.SmallCancellationGeometryFaceCapTopology
public import SmallPresentation.SmallCancellationGeometryFactorDisc

/-! Original vertex readings, factor support and marked shape under face capping. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap

open PermutationCycles
variable {D X H Q : Type*} [Finite D] [Group H] [Group Q]
    (P : RibbonMap D) (a : D) (L : RibbonLabelling P X H)

/-- Every original vertex retains its entire original departure list. -/
theorem old_vertexBoundary (d : D) :
    (map P a).vertexBoundary (.inl d) = (P.vertexBoundary d).map Sum.inl :=
  (cycleBoundary_map_injective P.rotation (map P a).rotation Sum.inl Sum.inl_injective
    (fun _ ↦ rfl) d).symm

/-- Every original complete based row word remains literally unchanged. -/
theorem old_vertexWord (h : H) (d : D) :
    (label P a L h).vertexWord (.inl d) = L.vertexWord d := by
  rw [RibbonLabelling.vertexWord, old_vertexBoundary, List.map_map]
  rfl

theorem old_cycle_darts (d : D) (e : D ⊕ Bool)
    (he : (map P a).rotation.SameCycle (.inl d) e) :
    ∃ e', e = .inl e' ∧ P.rotation.SameCycle d e' := by
  have hh := ((map P a).mem_vertexBoundary_iff _ _).mpr he
  rw [old_vertexBoundary] at hh
  obtain ⟨e', he', heq⟩ := List.mem_map.mp hh
  exact ⟨e', heq.symm, (P.mem_vertexBoundary_iff _ _).mp he'⟩

/-- No original old factor relation is changed by adding the marked cap. -/
theorem old_factorDisc (h : H) (d : D) (F : FactorDisc L d) :
    FactorDisc (label P a L h) (.inl d) := by
  constructor
  · intro e he
    obtain ⟨e', rfl, he'⟩ := old_cycle_darts P a d e he
    exact F.tag e' he'
  · intro e he
    obtain ⟨e', rfl, he'⟩ := old_cycle_darts P a d e he
    exact F.alternating e' he'
  · intro e he hs
    obtain ⟨e', rfl, he'⟩ := old_cycle_darts P a d e he
    exact F.negative e' he' hs
  · rw [old_vertexBoundary, List.map_map]
    exact F.product

/-- The added vertex is one factor-shaped marked boundary, not an extra attaching row. -/
theorem marked_shape (h : H) (ha : (L.arc a).2 = true) :
    FactorVertexShape (label P a L h) (.inr false) := by
  have only (d : D ⊕ Bool) (hd : (map P a).rotation.SameCycle (.inr false) d) :
      d = .inr false ∨ d = .inr true := by
    have hh := ((map P a).mem_vertexBoundary_iff _ _).mpr hd
    simpa only [marked_vertexBoundary, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hh
  constructor
  · intro d hd
    rcases only d hd with rfl | rfl <;> rfl
  · intro d hd
    rcases only d hd with rfl | rfl
    · rfl
    · exact (Bool.not_not _).symm
  · intro d hd hs
    rcases only d hd with rfl | rfl
    · change (L.arc a).2 = false at hs
      rw [ha] at hs
      contradiction
    · rfl

variable {q : H →* Q} (F : CornerPotential L q)

/-- Capping also retains the original quotient paths: both new edge ends have the same
potential, since the original exceptional face already maps to one in the quotient. -/
noncomputable def potential :
    CornerPotential (label P a L (L.faceValue (P.face a))) q where
  value := Sum.elim F.value (fun _ ↦ F.value a)
  edge := by
    rintro (d | b)
    · by_cases ha : d = a
      · subst d
        rw [edge_anchor]
        rfl
      · by_cases he : d = P.edge a
        · subst d
          rw [edge_mate]
          exact (F.edge a).symm
        · rw [edge_old P a d ha he]
          exact F.edge d
    · cases b
      · rw [edge_positive]
        exact F.edge a
      · rw [edge_negative]
        rfl
  rotation := by
    rintro (d | b)
    · exact F.rotation d
    · cases b
      · change F.value a = F.value a * q (L.faceValue (P.face a))
        rw [F.faceValue_map_one, mul_one]
      · change F.value a = F.value a * q 1
        rw [map_one, mul_one]

variable {A : Type*} (G : A → Type*) [∀ x, Group (G x)]
    (N : RibbonLabelling P A (Monoid.CoprodI G)) (C : RibbonLabelling.FactorCorners G N)

include C

/-- Opposite marker ends always lie on different coefficient faces. -/
theorem opposite_faces : ¬ P.face.SameCycle a (P.edge a) := by
  intro h
  have hh := constant_on_cycles P.face (RibbonLabelling.faceKey G N) C.face_key h
  have he := N.edge_arc a
  rw [RibbonLabelling.faceKey, RibbonLabelling.faceKey, he] at hh
  cases hs : (N.arc a).2 <;> simp [reverseLetter, hs] at hh

omit [Finite D] in
/-- The original factor-support laws extend over the newly marked coefficient. -/
theorem factorCorners (ha : (N.arc a).2 = true)
    (h : Monoid.CoprodI G)
    (hh : h ∈ (Monoid.CoprodI.of : G (N.arc a).1 →* Monoid.CoprodI G).range) :
    RibbonLabelling.FactorCorners G (label P a N h) := by
  constructor
  · rintro (d | b)
    · exact C.alternating d
    · cases b
      · rfl
      · exact (Bool.not_not _).symm
  · rintro (d | b) hd
    · exact C.positive_tag d hd
    · cases b <;> rfl
  · rintro (d | b) hd
    · exact C.negative_one d hd
    · cases b
      · change (N.arc a).2 = false at hd
        rw [ha] at hd
        contradiction
      · rfl
  · rintro (d | b)
    · exact C.coefficient d
    · cases b
      · exact hh
      · exact one_mem _

/-- The capped face coefficient belongs to precisely the new marked vertex's factor. -/
theorem cap_coefficient_mem :
    N.faceValue (P.face a) ∈
      (Monoid.CoprodI.of : G (N.arc a).1 →* Monoid.CoprodI G).range := by
  have hc := C.face_corner_mem a (P.face a)
    (Equiv.Perm.sameCycle_apply_right.mpr (.refl _ _))
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  apply inv_mem
  apply C.face_corner_mem a d
  exact Equiv.Perm.sameCycle_apply_left.mp ((P.mem_faceBoundary_iff _ _).mp hd)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.FaceCap
