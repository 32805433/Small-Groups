module

public import SmallPresentation.SmallCancellationDipolePairFactorDiscs
public import SmallPresentation.SmallCancellationDipoleRelativeSplice

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
open PermutationCycles
variable {A I : Type} (G : A → Type) [∀ x, Group (G x)]
    (length : I → ℕ) [∀ i, NeZero (length i)]
    (rows : ∀ i, Fin (length i) → Syllable G)
    {D : Type*} {P : RibbonMap D} (L : RibbonLabelling P A (Monoid.CoprodI G))
    (o : Origin length) (a b : D)
    (hforward : L.vertexWord a = Augmentation.word G length rows o)
    (hbackward : L.reverseVertexWord b = Augmentation.word G length rows o)
    (C : RibbonLabelling.FactorCorners G L)
    (f : Dart (length o.row) ↪ D)
    (hff : ∀ k, f (.inl k, false) = P.rotation^[2 * k.val] a)
    (hft : ∀ k, f (.inl k, true) = P.rotation^[2 * k.val + 1] a)
    (hsf : ∀ k, f (.inr k, false) = P.rotation.symm^[2 * k.rev.val + 1] b)
    (hst : ∀ k, f (.inr k, true) = P.rotation.symm^[2 * k.rev.val] b)

include hforward hbackward hff hft hsf hst in
theorem paired_arc (d : Dart (length o.row)) :
    L.arc (f d) = arc (fun k ↦ (syllableAt G length rows o k.val).1) d := by
  rcases d with ⟨k | k, phase⟩ <;> cases phase
  · rw [hff]
    exact congrArg Prod.fst (by simpa only [Augmentation.entry_even] using
      OppositeBand.forward_reading G length rows L a o hforward (2 * k.val) (by omega))
  · rw [hft]
    exact congrArg Prod.fst (by simpa only [Augmentation.entry_odd] using
      OppositeBand.forward_reading G length rows L a o hforward (2 * k.val + 1) (by omega))
  · rw [hsf]
    have hh := congrArg Prod.fst (OppositeBand.reverse_reading G length rows L b o
      hbackward (2 * k.rev.val + 1) (by have := k.rev.isLt; omega))
    have hr := congrArg reverseLetter hh
    simpa only [Augmentation.entry_odd, reverseLetter, Bool.not_not, arc, index, Bool.not_false, Bool.not_true, Prod.mk.eta] using hr
  · rw [hst]
    have hh := congrArg Prod.fst (OppositeBand.reverse_reading G length rows L b o
      hbackward (2 * k.rev.val) (by have := k.rev.isLt; omega))
    have hr := congrArg reverseLetter hh
    simpa only [Augmentation.entry_even, reverseLetter, Bool.not_not, arc, index, Bool.not_false, Bool.not_true, Prod.mk.eta] using hr

def rawCoefficient {n : ℕ} {H : Type*} [Group H] (g : Fin n → H) : Dart n → H
  | (.inl k, false) => g k
  | (.inr k, false) => (g k.rev)⁻¹
  | (_, true) => 1

include hforward hbackward C hff hft hsf hst in
theorem paired_corner (d : Dart (length o.row)) :
    L.corner (f d) = rawCoefficient (fun k ↦ includeSyllable G (syllableAt G length rows o k.val)) d := by
  have ha := paired_arc G length rows L o a b hforward hbackward f hff hft hsf hst
  rcases d with ⟨k | k, phase⟩ <;> cases phase
  · rw [hff]
    exact congrArg Prod.snd (by simpa only [Augmentation.entry_even] using
      OppositeBand.forward_reading G length rows L a o hforward (2 * k.val) (by omega))
  · exact C.negative_one _ (congrArg Prod.snd (ha (.inl k, true)))
  · rw [hsf]
    have hh := congrArg Prod.snd (OppositeBand.reverse_reading G length rows L b o
      hbackward (2 * k.rev.val) (by have := k.rev.isLt; omega))
    simpa only [Augmentation.entry_even, inv_inv, rawCoefficient] using congrArg Inv.inv hh
  · exact C.negative_one _ (congrArg Prod.snd (ha (.inr k, true)))

/-- Exact anchor transfer turns the two distinguished positive corners into one and
retains all other inverse-syllable coefficients. This calculation is in the original
coefficient group, independently of any quotient embedding. -/
theorem splice_corner {n : ℕ} {D X H : Type*} [Group H] {P : RibbonMap D}
    (L : RibbonLabelling P X H) (a : D) (anchor : Fin n) (g : Fin n → H)
    (f : Dart n ↪ D) (ha : f (.inl anchor, false) = a)
    (hp : f (.inr anchor.rev, false) = P.face a)
    (hraw : ∀ d, L.corner (f d) = rawCoefficient g d) (d : Dart n) :
    (P.edgeSpliceLabelling L a).corner (f d) = coefficient anchor g d := by
  classical
  change (if f d = a then 1 else L.corner (f d) *
    if f d = P.face a then L.corner a else 1) = _
  rw [← hp, ← ha, hraw d, hraw (.inl anchor, false)]
  simp only [f.injective.eq_iff]
  rcases d with ⟨k | k, phase⟩ <;> cases phase
  · simp [coefficient, rawCoefficient]
  · simp [coefficient, rawCoefficient]
  · have hk : k = anchor.rev ↔ k.rev = anchor := by
      constructor <;> intro h
      · simpa using congrArg Fin.rev h
      · simpa using congrArg Fin.rev h
    simp only [Prod.mk.injEq, Sum.inr.injEq, and_true, Sum.inr_ne_inl,
      ite_false, hk, rawCoefficient, coefficient]
    split_ifs with h
    · rw [h, inv_mul_cancel]
    · exact mul_one _
  · simp [coefficient, rawCoefficient]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
