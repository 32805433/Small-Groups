module

public import SmallPresentation.SmallCancellationGeometryMarkedPictureRealization

/-!
# Minimal marked counterexamples

The induction orders actual attaching vertices first and actual darts second. This
permits replacing a dipole by factor discs even when that operation increases the number
of factor vertices. No size is assigned to a chosen quotient-word representative.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

variable {A I : Type} {G : A → Type} [∀ a, Group (G a)]
    {length : I → ℕ} [∀ i, NeZero (length i)]
    {rows : ∀ i, Fin (length i) → Syllable G}
    {D : Type} [Fintype D] (T : MarkedRelativePicture G length rows D)

/-- Lexicographic minimality amongst all actual marked pictures for the same attaching rows. -/
structure Minimal : Prop where
  row_min : ∀ (E : Type) [Fintype E] (S : MarkedRelativePicture G length rows E),
    T.newCount ≤ S.newCount
  dart_min : ∀ (E : Type) [Fintype E] (S : MarkedRelativePicture G length rows E),
    S.newCount = T.newCount → Fintype.card D ≤ Fintype.card E

include T in
/-- An existing marked picture admits a least attaching count and then a least dart count. -/
theorem exists_minimal : ∃ (E : Type) (_ : Fintype E)
    (S : MarkedRelativePicture G length rows E), S.Minimal := by
  classical
  let R (n : ℕ) := ∃ (E : Type) (_ : Fintype E)
    (S : MarkedRelativePicture G length rows E), S.newCount = n
  have hR : ∃ n, R n := ⟨T.newCount, D, inferInstance, T, rfl⟩
  let n := Nat.find hR
  have hn : R n := Nat.find_spec hR
  let C (k : ℕ) := ∃ (E : Type) (_ : Fintype E)
    (S : MarkedRelativePicture G length rows E), S.newCount = n ∧ Fintype.card E = k
  have hC : ∃ k, C k := by
    obtain ⟨E, inst, S, hs⟩ := hn
    exact ⟨@Fintype.card E inst, E, inst, S, hs, rfl⟩
  obtain ⟨E, inst, S, hs, he⟩ := Nat.find_spec hC
  let : Fintype E := inst
  refine ⟨E, inst, S, ?_, ?_⟩
  · intro F _ U
    rw [hs]
    exact Nat.find_min' hR ⟨F, inferInstance, U, rfl⟩
  · intro F _ U hu
    rw [he]
    exact Nat.find_min' hC ⟨F, inferInstance, U, hu.trans hs, rfl⟩

/-- Any construction decreasing the actual row count contradicts minimality, regardless
of its new number of factor discs or darts. -/
theorem Minimal.not_fewer_rows (h : T.Minimal) {E : Type} [Fintype E]
    (S : MarkedRelativePicture G length rows E) (hs : S.newCount < T.newCount) : False :=
  (Nat.not_lt_of_ge (h.row_min E S)) hs

/-- At equal row count, a smaller marked component contradicts the secondary minimum. -/
theorem Minimal.not_fewer_darts (h : T.Minimal) {E : Type} [Fintype E]
    (S : MarkedRelativePicture G length rows E) (hr : S.newCount = T.newCount)
    (hd : Fintype.card E < Fintype.card D) : False :=
  (Nat.not_lt_of_ge (h.dart_min E S hr)) hd

/-- A surgery that adds no attaching rows and strictly removes darts contradicts
lexicographic minimality, even before equality of the attaching counts is established. -/
theorem Minimal.not_fewer_darts_of_rows_le (h : T.Minimal) {E : Type} [Fintype E]
    (S : MarkedRelativePicture G length rows E) (hr : S.newCount ≤ T.newCount)
    (hd : Fintype.card E < Fintype.card D) : False :=
  Minimal.not_fewer_darts T h S (Nat.le_antisymm hr (h.row_min E S)) hd

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRelativePicture

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)

/-- Excluding actual minimal marked pictures suffices for the exact original factor maps.
This separates the general realization argument from the geometric exclusion proof. -/
theorem factor_injective_of_no_minimal_picture
    (h : ∀ (D : Type) [Fintype D] (T : MarkedRelativePicture G length rows D),
      ¬T.Minimal) : ∀ a, Function.Injective (factorMap G length rows a) := by
  intro a
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  by_contra hne
  obtain ⟨D, inst, ⟨T⟩⟩ := exists_picture G length rows a g hg hne
  let : Fintype D := inst
  obtain ⟨E, inst', S, hs⟩ := T.exists_minimal
  let : Fintype E := inst'
  exact h E S hs

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.MarkedRealization
