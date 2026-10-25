module

public import SmallPresentation.SignedOverlap
public import SmallPresentation.RelativeSmallCancellation

/-! # The signed-code application of generic free-product small cancellation -/
@[expose] public section

namespace SmallPresentationStatements.SignedCoding
namespace Relative

abbrev Pair (d : ℕ) := {p : Fin d × Fin d // p.1 ≠ p.2}
abbrev Factor (d : ℕ) := Pair d ⊕ Fin d
abbrev Row (d : ℕ) := Pair d × Fin 2

abbrev FactorGroup {L d : ℕ} (Q : FP 2 L) : Factor d → Type
  | .inl _ => Q.Group
  | .inr _ => Multiplicative ℤ

instance factorGroup {L d : ℕ} (Q : FP 2 L) (a : Factor d) : Group (FactorGroup Q a) := by
  cases a <;> dsimp [FactorGroup] <;> infer_instance

abbrev rowLength {d : ℕ} (_ : Row d) := 33

def rows {L d : ℕ} (Q : FP 2 L) (a : Row d) (p : Fin 33) :
    RelativeSmallCancellation.Syllable (FactorGroup Q (d := d)) :=
  let c := coordinate a.2 p
  if c = 0 then ⟨.inl a.1, (PresentedGroup.of a.2)⁻¹⟩
  else ⟨.inr (if c.natAbs = 1 then a.1.val.1 else a.1.val.2), Multiplicative.ofAdd c⟩

def decode {L d : ℕ} (Q : FP 2 L) :
    RelativeSmallCancellation.Syllable (FactorGroup Q (d := d)) → Syllable Q.Group d
  | ⟨.inl a, x⟩ => .special a.val.1 a.val.2 x
  | ⟨.inr v, x⟩ => .ordinary v x.toAdd

def forgetFactor {d : ℕ} : Factor d → (Fin d × Fin d) ⊕ Fin d
  | .inl a => .inl a.val
  | .inr v => .inr v

theorem decode_injective {L d : ℕ} (Q : FP 2 L) :
    Function.Injective (decode Q (d := d)) := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hh := Syllable.special.inj h
      have hab : a = b := Subtype.ext (Prod.ext hh.1 hh.2.1)
      cases hab
      cases hh.2.2
      rfl
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have hh := Syllable.ordinary.inj h
      cases hh.1
      have hxy : x = y := Multiplicative.toAdd.injective hh.2
      cases hxy
      rfl

theorem decode_factor {L d : ℕ} (Q : FP 2 L)
    (s : RelativeSmallCancellation.Syllable (FactorGroup Q (d := d))) :
    (decode Q s).factor = forgetFactor s.1 := by
  rcases s with ⟨a, x⟩
  cases a <;> rfl

theorem decode_nontrivial {L d : ℕ} (Q : FP 2 L)
    (s : RelativeSmallCancellation.Syllable (FactorGroup Q (d := d)))
    (h : (decode Q s).Nontrivial) : s.2 ≠ 1 := by
  rcases s with ⟨a, x⟩
  cases a with
  | inl a => exact h
  | inr v =>
    intro hx
    apply h
    exact congrArg Multiplicative.toAdd hx

theorem decode_oriented {L d : ℕ} (Q : FP 2 L) (a : Row d) (b : Bool) (p : Fin 33) :
    decode Q (RelativeSmallCancellation.oriented (FactorGroup Q) rowLength (rows Q) a b p) =
      syllable (PresentedGroup.of (rels := Q.relSet)) a.1.val.1 a.1.val.2 a.2 b p := by
  cases b
  · by_cases hc : coordinate a.2 (-p) = 0
    · have hrow : rows Q a (-p) = ⟨.inl a.1, (PresentedGroup.of a.2)⁻¹⟩ := by
        simp only [rows, ite_eq_left hc]
      simp only [RelativeSmallCancellation.oriented, Bool.false_eq_true, ite_false, hrow]
      simp [RelativeSmallCancellation.inverseSyllable, decode, syllable, orientedCoordinate, hc]
    · have hrow : rows Q a (-p) =
          ⟨.inr (if (coordinate a.2 (-p)).natAbs = 1 then a.1.val.1 else a.1.val.2),
            Multiplicative.ofAdd (coordinate a.2 (-p))⟩ := by
        simp only [rows, ite_eq_right hc]
      simp only [RelativeSmallCancellation.oriented, Bool.false_eq_true, ite_false, hrow]
      simp [RelativeSmallCancellation.inverseSyllable, decode, syllable, orientedCoordinate, hc]
  · by_cases hc : coordinate a.2 p = 0 <;>
      simp [RelativeSmallCancellation.oriented, rows, decode, syllable, orientedCoordinate, hc]

private theorem ofNat_offset (p : Fin 33) (t : Fin 3) :
    p + Fin.ofNat 33 t.val = offset p t := by
  congr 1
  apply Fin.ext
  change t.val % 33 = t.val
  exact Nat.mod_eq_of_lt (by omega)

theorem rows_triple_injective {L d : ℕ} (Q : FP 2 L) :
    RelativeSmallCancellation.TripleInjective (FactorGroup Q) rowLength (rows Q (d := d)) := by
  intro a b h
  rcases a with ⟨⟨pair, j⟩, sign, p⟩
  rcases b with ⟨⟨pair', j'⟩, sign', p'⟩
  have hh : ∀ t : Fin 3,
      syllable (PresentedGroup.of (rels := Q.relSet)) pair.val.1 pair.val.2 j sign (offset p t) =
      syllable (PresentedGroup.of (rels := Q.relSet)) pair'.val.1 pair'.val.2 j' sign' (offset p' t) := by
    intro t
    have ht := congrArg (decode Q) (h t)
    simpa only [RelativeSmallCancellation.syllableAt, decode_oriented, ofNat_offset] using ht
  obtain ⟨hr, hu, hrot⟩ := triple_determines_row _ _ _ _ _ (j, sign, p) (j', sign', p') hh
  have hpairs : pair = pair' := Subtype.ext (Prod.ext hr hu)
  have hj : j = j' := congrArg Prod.fst hrot
  have hs : sign = sign' := congrArg (fun a : Rotation ↦ a.2.1) hrot
  have hp : p = p' := congrArg (fun a : Rotation ↦ a.2.2) hrot
  cases hpairs
  cases hj
  cases hs
  cases hp
  rfl

theorem rows_nontrivial {L d : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (a : Row d) (p : Fin 33) : (rows Q a p).2 ≠ 1 := by
  apply decode_nontrivial Q
  change (decode Q (RelativeSmallCancellation.oriented (FactorGroup Q) rowLength
    (rows Q) a true p)).Nontrivial
  rw [decode_oriented]
  exact syllable_nontrivial _ (noncyclic_generator_ne_one Q hQ) _ _ _ _ _

theorem rows_cyclically_reduced {L d : ℕ} (Q : FP 2 L) (a : Row d) (p : Fin 33) :
    (rows Q a p).1 ≠ (rows Q a (p + 1)).1 := by
  intro h
  have hh := congrArg forgetFactor h
  rw [← decode_factor Q, ← decode_factor Q] at hh
  change (decode Q (RelativeSmallCancellation.oriented (FactorGroup Q) rowLength
    (rows Q) a true p)).factor =
    (decode Q (RelativeSmallCancellation.oriented (FactorGroup Q) rowLength
      (rows Q) a true (p + 1))).factor at hh
  rw [decode_oriented, decode_oriented] at hh
  exact syllable_cyclically_reduced _ _ _ a.1.property _ _ _ hh

abbrev Group {L d : ℕ} (Q : FP 2 L) :=
  RelativeSmallCancellation.Quotient (FactorGroup Q (d := d)) rowLength (rows Q)

def factorMap {L d : ℕ} (Q : FP 2 L) (a : Factor d) : FactorGroup Q a →* Group Q (d := d) :=
  RelativeSmallCancellation.factorMap _ _ _ a

theorem factorMap_injective {L d : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group) (a : Factor d) :
    Function.Injective (factorMap Q a) :=
  (RelativeSmallCancellation.short_overlap_factor_injection_and_torsion
    (FactorGroup Q) rowLength (rows Q) (rows_nontrivial Q hQ) (rows_cyclically_reduced Q)
    (fun _ ↦ by norm_num [rowLength]) (rows_triple_injective Q)).1 a

theorem group_torsionfree {L d : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (hT : IsMulTorsionFree Q.Group) : IsMulTorsionFree (Group Q (d := d)) := by
  apply (RelativeSmallCancellation.short_overlap_factor_injection_and_torsion
    (FactorGroup Q) rowLength (rows Q) (rows_nontrivial Q hQ) (rows_cyclically_reduced Q)
    (fun _ ↦ by norm_num [rowLength]) (rows_triple_injective Q)).2
  intro a
  cases a <;> dsimp [FactorGroup]
  · exact hT
  · infer_instance

end Relative
end SmallPresentationStatements.SignedCoding
