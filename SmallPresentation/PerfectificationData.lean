module

public import SmallPresentation.ConversionWords
public import SmallPresentation.RelativeSmallCancellation

/-! # The exact free-product rows for perfectification, including trivial coefficients -/
@[expose] public section

namespace SmallPresentationStatements.Conversion.Relative

abbrev Row (k : ℕ) := Fin k ⊕ Fin 2
abbrev Factor := Unit ⊕ Fin 2

abbrev FactorGroup {k μ : ℕ} (T : FP k μ) : Factor → Type
  | .inl _ => T.Group
  | .inr _ => Multiplicative ℤ

instance factorGroup {k μ : ℕ} (T : FP k μ) (a : Factor) : Group (FactorGroup T a) := by
  cases a <;> dsimp [FactorGroup] <;> infer_instance

def markerList {k : ℕ} : Row k → List ℕ
  | .inl i => (List.range' 1 32).map fun l ↦ 2000 + 32 * (i.val + 1) + l
  | .inr j => if j = 0 then dummyExponents₁ else dummyExponents₂

theorem markerList_length_cases {k : ℕ} (i : Row k) :
    (markerList i).length = 32 ∨ (markerList i).length = 33 := by
  cases i with
  | inl i => exact Or.inl (by simp [markerList])
  | inr j =>
    by_cases h : j = 0
    · exact Or.inl (by simp [markerList, h, dummyExponents₁_length_sum.1])
    · exact Or.inr (by simp [markerList, h, dummyExponents₂_length_sum.1])

def coefficient {k μ : ℕ} (T : FP k μ) : Row k → T.Group
  | .inl i => (PresentedGroup.of i)⁻¹
  | .inr _ => 1

noncomputable def special {k μ : ℕ} (T : FP k μ) (i : Row k) : Bool := by
  classical
  exact decide (coefficient T i ≠ 1)

theorem special_iff {k μ : ℕ} (T : FP k μ) (i : Row k) :
    special T i = true ↔ coefficient T i ≠ 1 := by
  classical
  simp [special]

@[simp] theorem special_dummy {k μ : ℕ} (T : FP k μ) (j : Fin 2) :
    special T (.inr j) = false := by
  classical
  simp [special, coefficient]

noncomputable def rowLength {k μ : ℕ} (T : FP k μ) (i : Row k) : ℕ :=
  2 * (markerList i).length + (special T i).toNat

instance rowLength_neZero {k μ : ℕ} (T : FP k μ) (i : Row k) : NeZero (rowLength T i) := by
  constructor
  have h := markerList_length_cases i
  dsimp [rowLength]
  omega

noncomputable def rows {k μ : ℕ} (T : FP k μ) (i : Row k) (p : Fin (rowLength T i)) :
    RelativeSmallCancellation.Syllable (FactorGroup T) :=
  if h : p.val < (special T i).toNat then ⟨.inl (), coefficient T i⟩
  else if (p.val - (special T i).toNat) % 2 = 0 then ⟨.inr 0, Multiplicative.ofAdd 1⟩
  else ⟨.inr 1, Multiplicative.ofAdd
    ((markerList i).get ⟨(p.val - (special T i).toNat) / 2, by
      have hp := p.isLt
      dsimp [rowLength] at hp
      omega⟩ : ℤ)⟩

abbrev RelativeGroup {k μ : ℕ} (T : FP k μ) :=
  RelativeSmallCancellation.Quotient (FactorGroup T) (rowLength T) (rows T)

noncomputable def factorMap {k μ : ℕ} (T : FP k μ) (a : Factor) :
    FactorGroup T a →* RelativeGroup T :=
  RelativeSmallCancellation.factorMap _ _ _ a

end SmallPresentationStatements.Conversion.Relative
