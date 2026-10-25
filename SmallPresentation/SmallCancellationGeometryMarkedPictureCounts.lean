module

public import SmallPresentation.SmallCancellationGeometryMarkedMinimality

/-! Comparing actual attaching counts under surgery and component restriction. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D E : Type} [Fintype D] [Fintype E]
    (T : MarkedRelativePicture G length rows D) (S : MarkedRelativePicture G length rows E)

/-- Choose an actual incidence of an actual attaching vertex. -/
noncomputable def representative (v : T.NewVertex) : {d // T.IsNew d} :=
  ⟨Classical.choose v.property, (Classical.choose_spec v.property).2⟩

theorem representative_vertex (v : T.NewVertex) :
    T.map.vertexOf (T.representative v).val = v.val := (Classical.choose_spec v.property).1

variable (f : {d // S.IsNew d} → {d // T.IsNew d})
    (hf : ∀ d e, S.map.rotation.SameCycle d.val e.val ↔
      T.map.rotation.SameCycle (f d).val (f e).val)

/-- A cycle-reflecting map on the retained attaching incidences induces an embedding
of their actual vertex quotients. There is no requirement to retain old vertices. -/
noncomputable def newVertexEmbedding : S.NewVertex ↪ T.NewVertex where
  toFun v := ⟨T.map.vertexOf (f (S.representative v)).val,
    (f (S.representative v)).val, rfl, (f (S.representative v)).property⟩
  inj' := by
    intro v w h
    have hv : T.map.rotation.SameCycle (f (S.representative v)).val
        (f (S.representative w)).val := Quotient.exact (congrArg Subtype.val h)
    have hs : S.map.vertexOf (S.representative v).val =
        S.map.vertexOf (S.representative w).val := Quotient.sound ((hf _ _).mpr hv)
    rw [S.representative_vertex, S.representative_vertex] at hs
    exact Subtype.ext hs

include f hf in
/-- Retaining distinct actual attaching vertices cannot increase their number. -/
theorem newCount_le_of_cycle_embedding : S.newCount ≤ T.newCount :=
  Fintype.card_le_of_injective _ (T.newVertexEmbedding S f hf).injective

include hf in
/-- Omitting one original attaching vertex gives a strict decrease, even if factor discs
or marked-boundary darts have been added elsewhere. -/
theorem newCount_lt_of_missing (d : D) (hd : T.IsNew d)
    (hmiss : ∀ e, ¬T.map.rotation.SameCycle d (f e).val) : S.newCount < T.newCount := by
  let v : T.NewVertex := ⟨T.map.vertexOf d, d, rfl, hd⟩
  apply Fintype.card_lt_of_injective_of_notMem (T.newVertexEmbedding S f hf)
    (T.newVertexEmbedding S f hf).injective (b := v)
  rintro ⟨w, hw⟩
  have hh : T.map.vertexOf (f (S.representative w)).val = T.map.vertexOf d :=
    congrArg Subtype.val hw
  exact hmiss (S.representative w) (Quotient.exact hh.symm)

include hf in
/-- A minimal marked picture cannot lose an actual attaching vertex under any such
concrete diagram construction. -/
theorem Minimal.not_missing_vertex (hmin : T.Minimal) (d : D) (hd : T.IsNew d)
    (hmiss : ∀ e, ¬T.map.rotation.SameCycle d (f e).val) : False :=
  (Nat.not_lt_of_ge (hmin.row_min E S)) (T.newCount_lt_of_missing S f hf d hd hmiss)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture
