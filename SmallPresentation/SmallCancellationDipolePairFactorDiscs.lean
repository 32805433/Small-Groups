module

public import SmallPresentation.SmallCancellationGeometryPositiveRefinement
public import SmallPresentation.SmallCancellationGeometryFactorDisc
public import SmallPresentation.SmallCancellationDipoleRelativeFactorFaces

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
open PermutationCycles

abbrev Dart (n : ℕ) := (Fin n ⊕ Fin n) × Bool

def index {n : ℕ} : Dart n → Fin n
  | (.inl k, _) => k
  | (.inr k, _) => k.rev

def arc {n : ℕ} {X : Type*} (tag : Fin n → X) (d : Dart n) : X × Bool :=
  (tag (index d), !d.2)

def coefficient {n : ℕ} {H : Type*} [Group H] (anchor : Fin n)
    (g : Fin n → H) : Dart n → H
  | (.inl k, false) => if k = anchor then 1 else g k
  | (.inr k, false) => if k.rev = anchor then 1 else (g k.rev)⁻¹
  | (_, true) => 1

/-- Explicit local potential on each inverse-syllable block. It takes values in the
coefficient group itself, so its telescoping uses no factor-injectivity assumption. -/
def value {n : ℕ} {H : Type*} [Group H] (anchor : Fin n)
    (g : Fin n → H) : Dart n → H
  | (.inl _, false) => 1
  | (.inl k, true) => if k = anchor then 1 else g k
  | (.inr k, false) => if k.rev = anchor then 1 else g k.rev
  | (.inr _, true) => 1

/-- Four-cycles away from the spliced anchor and two two-cycles at the anchor. -/
def next {n : ℕ} (anchor : Fin n) : Dart n → Dart n
  | (.inl k, false) => if k = anchor then (.inr k.rev, true) else (.inl k, true)
  | (.inl k, true) => (.inr k.rev, false)
  | (.inr k, false) => if k.rev = anchor then (.inl k.rev, true) else (.inr k, true)
  | (.inr k, true) => (.inl k.rev, false)

theorem index_next {n : ℕ} (anchor : Fin n) (d : Dart n) :
    index (next anchor d) = index d := by
  rcases d with ⟨k | k, b⟩ <;> cases b <;>
    simp only [next] <;> (try split_ifs) <;> simp [index]

theorem phase_next {n : ℕ} (anchor : Fin n) (d : Dart n) :
    (next anchor d).2 = !d.2 := by
  rcases d with ⟨k | k, b⟩ <;> cases b <;>
    simp only [next] <;> (try split_ifs) <;> rfl

theorem value_next {n : ℕ} {H : Type*} [Group H] (anchor : Fin n)
    (g : Fin n → H) (d : Dart n) :
    value anchor g (next anchor d) = value anchor g d * coefficient anchor g d := by
  rcases d with ⟨k | k, b⟩ <;> cases b <;>
    simp only [next] <;> (try split_ifs) <;> simp_all [value, coefficient]

/-- Reclassifying the matched inverse rows into these factor blocks produces genuine
old factor relations, including the two coefficient-one anchor blocks. -/
theorem factorDisc {n : ℕ} {X H : Type*} [Group H]
    (anchor : Fin n) (tag : Fin n → X) (g : Fin n → H)
    (P : RibbonMap (Dart n)) (hrotation : ∀ d, P.rotation d = next anchor d)
    (L : RibbonLabelling P X H) (harc : ∀ d, L.arc d = arc tag d)
    (hcorner : ∀ d, L.corner d = coefficient anchor g d) (d : Dart n) :
    FactorDisc L d := by
  have hi : ∀ e, index (P.rotation e) = index e := fun e ↦ by
    rw [hrotation]; exact index_next anchor e
  constructor
  · intro e he
    rw [harc, harc]
    exact congrArg tag (constant_on_cycles P.rotation index hi he).symm
  · intro e he
    rw [harc, harc]
    change (!(P.rotation e).2) = !(!e.2)
    rw [hrotation, phase_next]
  · intro e he hneg
    rw [harc] at hneg
    rw [hcorner]
    rcases e with ⟨k | k, b⟩ <;> cases b <;> simp_all [arc, coefficient]
  · apply cycleProduct_eq_one_of_potential P.rotation (value anchor g) L.corner
    intro e
    rw [hrotation, hcorner]
    exact value_next anchor g e

theorem pairFactorRotation_apply {n : ℕ} (anchor : Fin n) (d : Dart n) :
    pairFactorRotation anchor d = next anchor d := by
  rcases d with ⟨k | k, b⟩ <;> cases b <;>
    simp [pairFactorRotation, cutAt_apply, doublePerm, RowDeletion.interchange,
      reverseFin, next, Equiv.swap_apply_def] <;> split_ifs <;> simp_all
  rename_i hne he
  exact hne (by simpa using congrArg Fin.rev he)

/-- The explicit blocks may be embedded in a larger mixed picture; their edges need
not remain within the selected pair. Only their complete vertex rotations matter. -/
theorem factorDisc_of_embedding {n : ℕ} {D X H : Type*} [Finite D] [Group H]
    (anchor : Fin n) (tag : Fin n → X) (g : Fin n → H)
    (P : RibbonMap D) (L : RibbonLabelling P X H) (f : Dart n ↪ D)
    (hrotation : ∀ d, P.rotation (f d) = f (pairFactorRotation anchor d))
    (harc : ∀ d, L.arc (f d) = arc tag d)
    (hcorner : ∀ d, L.corner (f d) = coefficient anchor g d) (d : Dart n) :
    FactorDisc L (f d) := by
  have hb (d) : P.vertexBoundary (f d) =
      (cycleBoundary (pairFactorRotation anchor) d).map f :=
    (cycleBoundary_map_injective _ _ f f.injective (fun e ↦ (hrotation e).symm) d).symm
  have hi : ∀ e, index (pairFactorRotation anchor e) = index e := fun e ↦ by
    rw [pairFactorRotation_apply]; exact index_next anchor e
  have inside (e : D) (he : P.rotation.SameCycle (f d) e) :
      ∃ k, e = f k ∧ (pairFactorRotation anchor).SameCycle d k := by
    have hh := (P.mem_vertexBoundary_iff _ _).mpr he
    rw [hb] at hh
    obtain ⟨k, hk, heq⟩ := List.mem_map.mp hh
    refine ⟨k, heq.symm, ?_⟩
    obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hk
    exact Equiv.Perm.sameCycle_pow_right.mpr (.refl _ _)
  constructor
  · intro e he
    obtain ⟨k, rfl, hk⟩ := inside e he
    rw [harc, harc]
    exact congrArg tag (constant_on_cycles _ index hi hk).symm
  · intro e he
    obtain ⟨k, rfl, hk⟩ := inside e he
    rw [hrotation, harc, harc]
    change (!(pairFactorRotation anchor k).2) = !(!k.2)
    rw [pairFactorRotation_apply, phase_next]
  · intro e he hneg
    obtain ⟨k, rfl, hk⟩ := inside e he
    rw [harc] at hneg
    rw [hcorner]
    rcases k with ⟨k | k, b⟩ <;> cases b <;> simp_all [arc, coefficient]
  · rw [hb, List.map_map]
    have hw : L.corner ∘ f = coefficient anchor g := funext hcorner
    rw [hw]
    apply cycleProduct_eq_one_of_potential _ (value anchor g)
    intro e
    rw [pairFactorRotation_apply]
    exact value_next anchor g e

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks
