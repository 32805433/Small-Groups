module

public import SmallPresentation.PerfectificationData
public import SmallPresentation.PositiveMarkerOverlap

/-! # The actual perfectification rows satisfy the generic overlap hypotheses -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SmallPresentationStatements.Conversion.Relative

variable {k μ : ℕ}

theorem markerList_input_get (i : Fin k) (p : Fin (markerList (.inl i)).length) :
    (markerList (.inl i)).get p = 2000 + 32 * (i.val + 1) + (p.val + 1) := by
  simp [markerList, List.get_eq_getElem, Nat.add_comm]

theorem markerList_dummy_bounds (j : Fin 2) (p : Fin (markerList (Sum.inr j : Row k)).length) :
    2 ≤ (markerList (Sum.inr j : Row k)).get p ∧
      (markerList (Sum.inr j : Row k)).get p ≤ 1163 := by
  have h₁ : ∀ p : Fin dummyExponents₁.length,
      2 ≤ dummyExponents₁.get p ∧ dummyExponents₁.get p ≤ 1163 := by decide
  have h₂ : ∀ p : Fin dummyExponents₂.length,
      2 ≤ dummyExponents₂.get p ∧ dummyExponents₂.get p ≤ 1163 := by decide
  fin_cases j
  · exact h₁ p
  · exact h₂ p

theorem markerList_ge_two (i : Row k) (p : Fin (markerList i).length) :
    2 ≤ (markerList i).get p := by
  cases i with
  | inl i => rw [markerList_input_get]; omega
  | inr j => exact (markerList_dummy_bounds j p).1

private theorem dummy_marker_injective (j j' : Fin 2)
    (p : Fin (markerList (Sum.inr j : Row k)).length)
    (q : Fin (markerList (Sum.inr j' : Row k)).length)
    (h : (markerList (Sum.inr j : Row k)).get p = (markerList (Sum.inr j' : Row k)).get q) :
    j = j' ∧ p.val = q.val := by
  have h₁ : ∀ p q : Fin dummyExponents₁.length,
      dummyExponents₁.get p = dummyExponents₁.get q → p.val = q.val := by decide
  have h₂ : ∀ p q : Fin dummyExponents₂.length,
      dummyExponents₂.get p = dummyExponents₂.get q → p.val = q.val := by decide
  have h₁₂ : ∀ (p : Fin dummyExponents₁.length) (q : Fin dummyExponents₂.length),
      dummyExponents₁.get p ≠ dummyExponents₂.get q := by decide
  fin_cases j <;> fin_cases j'
  · exact ⟨rfl, h₁ p q h⟩
  · exact (h₁₂ p q h).elim
  · exact (h₁₂ q p h.symm).elim
  · exact ⟨rfl, h₂ p q h⟩

theorem markerList_get_injective :
    Function.Injective (fun p : Σ i : Row k, Fin (markerList i).length ↦ (markerList p.1).get p.2) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  dsimp only at h
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rw [markerList_input_get, markerList_input_get] at h
      have hp : p.val < 32 := by simpa [markerList] using p.isLt
      have hq : q.val < 32 := by simpa [markerList] using q.isLt
      have hij : i = j := Fin.ext (by omega)
      cases hij
      apply congrArg (Sigma.mk (Sum.inl i))
      exact Fin.ext (by omega)
    | inr j =>
      rw [markerList_input_get] at h
      have hq := (markerList_dummy_bounds j q).2
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [markerList_input_get] at h
      have hp := (markerList_dummy_bounds i p).2
      omega
    | inr j =>
      obtain ⟨hij, hpq⟩ := dummy_marker_injective i j p q h
      cases hij
      exact congrArg (Sigma.mk (Sum.inr i)) (Fin.ext hpq)

noncomputable def markerFamily (T : FP k μ) : PositiveMarkerOverlap.Family (Row k) where
  blocks i := (markerList i).length
  blocks_cases := markerList_length_cases
  marker i := (markerList i).get
  marker_ge_two := markerList_ge_two
  marker_injective := markerList_get_injective
  special := special T

def scalar (T : FP k μ) : RelativeSmallCancellation.Syllable (FactorGroup T) → ℤ
  | ⟨.inl _, _⟩ => 0
  | ⟨.inr _, x⟩ => x.toAdd

theorem scalar_rows (T : FP k μ) (i : Row k) (p : Fin (rowLength T i)) :
    scalar T (rows T i p) = (markerFamily T).coordinate i p := by
  unfold rows PositiveMarkerOverlap.Family.coordinate markerFamily
  split
  · rfl
  · split <;> rfl

theorem scalar_inverse (T : FP k μ) (s : RelativeSmallCancellation.Syllable (FactorGroup T)) :
    scalar T (RelativeSmallCancellation.inverseSyllable (FactorGroup T) s) = -scalar T s := by
  rcases s with ⟨a, x⟩
  cases a <;> rfl

theorem scalar_at (T : FP k μ) (a : RelativeSmallCancellation.Origin (rowLength T)) (t : ℕ) :
    scalar T (RelativeSmallCancellation.syllableAt (FactorGroup T) (rowLength T) (rows T) a t) =
      (markerFamily T).signedAt a t := by
  cases h : a.forward <;>
    simp [RelativeSmallCancellation.syllableAt, RelativeSmallCancellation.oriented,
      PositiveMarkerOverlap.Family.signedAt, PositiveMarkerOverlap.Family.point,
      h, scalar_rows, scalar_inverse]

theorem rows_triple_injective (T : FP k μ) :
    RelativeSmallCancellation.TripleInjective (FactorGroup T) (rowLength T) (rows T) := by
  intro a b h
  apply (markerFamily T).triple_injective a b
  intro t
  simpa only [scalar_at] using congrArg (scalar T) (h t)

private def SyllableNontrivial (T : FP k μ) (s : RelativeSmallCancellation.Syllable (FactorGroup T)) : Prop := s.2 ≠ 1

theorem rows_nontrivial (T : FP k μ) (i : Row k) (p : Fin (rowLength T i)) :
    (rows T i p).2 ≠ 1 := by
  change SyllableNontrivial T (rows T i p)
  unfold rows
  split
  · rename_i hp
    change coefficient T i ≠ 1
    apply (special_iff T i).mp
    cases hs : special T i <;> simp_all
  · split
    · change (Multiplicative.ofAdd (1 : ℤ)) ≠ Multiplicative.ofAdd 0
      decide
    · change (Multiplicative.ofAdd ((markerList i).get _ : ℤ)) ≠ 1
      intro h
      have hz := congrArg Multiplicative.toAdd h
      have hm := markerList_ge_two i ⟨(p.val - (special T i).toNat) / 2, by
        have hp' := p.isLt
        dsimp [rowLength] at hp'
        omega⟩
      change ((markerList i).get _ : ℤ) = 0 at hz
      omega

def positionTag (s p : ℕ) : ℕ := if p < s then 0 else if (p - s) % 2 = 0 then 1 else 2

private theorem shape_adjacent (b : ℕ) (hb : b = 32 ∨ b = 33) (s : Bool)
    (p : Fin (2 * b + s.toNat)) :
    positionTag s.toNat p.val ≠ positionTag s.toNat ((p.val + 1) % (2 * b + s.toNat)) := by
  rcases hb with rfl | rfl <;> cases s <;> revert p <;> decide

def factorTag : Factor → ℕ
  | .inl _ => 0
  | .inr i => i.val + 1

theorem rows_factor_tag (T : FP k μ) (i : Row k) (p : Fin (rowLength T i)) :
    factorTag (rows T i p).1 = positionTag (special T i).toNat p.val := by
  unfold rows positionTag
  split
  · rfl
  · split <;> rfl

theorem rowLength_ge (T : FP k μ) (i : Row k) : 64 ≤ rowLength T i := by
  have h := markerList_length_cases i
  dsimp [rowLength]
  omega

theorem rows_cyclically_reduced (T : FP k μ) (i : Row k) (p : Fin (rowLength T i)) :
    (rows T i p).1 ≠ (rows T i (p + 1)).1 := by
  intro h
  have hh := congrArg factorTag h
  rw [rows_factor_tag, rows_factor_tag] at hh
  have hv : (p + 1).val = (p.val + 1) % rowLength T i := by
    change (p.val + 1 % rowLength T i) % rowLength T i = _
    have h1 : 1 % rowLength T i = 1 := Nat.mod_eq_of_lt (by have h := rowLength_ge T i; omega)
    rw [h1]
  rw [hv] at hh
  exact shape_adjacent (markerList i).length (markerList_length_cases i) (special T i) p hh

theorem factorMap_injective (T : FP k μ) (a : Factor) :
    Function.Injective (factorMap T a) :=
  (RelativeSmallCancellation.short_overlap_factor_injection_and_torsion
    (FactorGroup T) (rowLength T) (rows T) (rows_nontrivial T) (rows_cyclically_reduced T)
    (fun i ↦ by have h := rowLength_ge T i; omega) (rows_triple_injective T)).1 a

theorem relativeGroup_torsionfree (T : FP k μ) (hT : IsMulTorsionFree T.Group) :
    IsMulTorsionFree (RelativeGroup T) := by
  apply (RelativeSmallCancellation.short_overlap_factor_injection_and_torsion
    (FactorGroup T) (rowLength T) (rows T) (rows_nontrivial T) (rows_cyclically_reduced T)
    (fun i ↦ by have h := rowLength_ge T i; omega) (rows_triple_injective T)).2
  intro a
  cases a with
  | inl _ => exact hT
  | inr _ => infer_instance

end SmallPresentationStatements.Conversion.Relative
