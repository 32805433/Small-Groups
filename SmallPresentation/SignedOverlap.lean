module

public import SmallPresentation.SignedCoding
public import SmallPresentation.StructuralDefinitions
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Finite syllable certificates for the signed codes

The ordinary coordinates retain the actual signed powers in `V₁,V₂`; the
single special-factor syllable has coordinate zero. Three consecutive
coordinates distinguish every code, orientation, and cyclic starting position.
-/
@[expose] public section

namespace SmallPresentationStatements.SignedCoding

/-- Coordinate zero marks the special factor; odd positions are the `x` syllables. -/
def coordinate (j : Fin 2) (p : Fin 33) : ℤ :=
  if p.val = 0 then 0 else if p.val % 2 = 1 then 1
  else if p.val = 32 then if j.val = 0 then -150 else -376
  else (p.val / 2 + 1 + 15 * j.val : ℕ)

/-- Inversion fixes the distinguished cyclic origin and reverses the remaining syllables. -/
def orientedCoordinate (j : Fin 2) (forward : Bool) (p : Fin 33) : ℤ :=
  if forward then coordinate j p else -coordinate j (-p)

abbrev Rotation := Fin 2 × Bool × Fin 33

def coordinateSignature (a : Rotation) : ℤ × ℤ × ℤ :=
  (orientedCoordinate a.1 a.2.1 a.2.2,
    orientedCoordinate a.1 a.2.1 (a.2.2 + 1),
    orientedCoordinate a.1 a.2.1 (a.2.2 + 2))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem coordinateSignature_injective : Function.Injective coordinateSignature := by
  simp only [Function.Injective, Prod.forall]
  decide

def offset (p : Fin 33) (t : Fin 3) : Fin 33 := p + ⟨t.val, by omega⟩

set_option maxRecDepth 10000 in
theorem triple_contains_x (a : Rotation) :
    ∃ t : Fin 3, (orientedCoordinate a.1 a.2.1 (offset a.2.2 t)).natAbs = 1 := by
  rcases a with ⟨j, b, p⟩
  revert j b p
  decide

set_option maxRecDepth 10000 in
theorem triple_contains_y (a : Rotation) :
    ∃ t : Fin 3, 2 ≤ (orientedCoordinate a.1 a.2.1 (offset a.2.2 t)).natAbs := by
  rcases a with ⟨j, b, p⟩
  revert j b p
  decide

/-- Syllables retain both the free-product factor label and the actual group element. -/
inductive Syllable (G : Type*) (d : ℕ) where
  | special (r u : Fin d) (value : G)
  | ordinary (vertex : Fin d) (power : ℤ)

namespace Syllable

def exponent {G : Type*} {d : ℕ} : Syllable G d → ℤ
  | special _ _ _ => 0
  | ordinary _ n => n

def factor {G : Type*} {d : ℕ} : Syllable G d → (Fin d × Fin d) ⊕ Fin d
  | special r u _ => .inl (r, u)
  | ordinary v _ => .inr v

def Nontrivial {G : Type*} [Group G] {d : ℕ} : Syllable G d → Prop
  | special _ _ g => g ≠ 1
  | ordinary _ n => n ≠ 0

end Syllable

/-- The oriented cyclic row `z_j⁻¹ V_j`, indexed by its 33 free-product syllables. -/
def syllable {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (forward : Bool) (p : Fin 33) : Syllable G d :=
  let c := orientedCoordinate j forward p
  if c = 0 then .special r u (if forward then (z j)⁻¹ else z j)
  else .ordinary (if c.natAbs = 1 then r else u) c

@[simp] theorem syllable_exponent {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (forward : Bool) (p : Fin 33) :
    (syllable z r u j forward p).exponent = orientedCoordinate j forward p := by
  simp only [syllable]
  split
  · rename_i h
    exact h.symm
  · rfl

theorem syllable_nontrivial {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (hz : ∀ j, z j ≠ 1) (r u : Fin d) (j : Fin 2) (forward : Bool) (p : Fin 33) :
    (syllable z r u j forward p).Nontrivial := by
  simp only [syllable]
  split
  · cases forward <;> simp [Syllable.Nontrivial, hz]
  · assumption

/-- Equality of three literal syllables determines the code, orientation, and rotation. -/
theorem triple_determines_rotation {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u r' u' : Fin d) (a b : Rotation)
    (h : ∀ t : Fin 3,
      syllable z r u a.1 a.2.1 (offset a.2.2 t) =
        syllable z r' u' b.1 b.2.1 (offset b.2.2 t)) : a = b := by
  apply coordinateSignature_injective
  apply Prod.ext
  · have h₀ := congrArg Syllable.exponent (h 0)
    simpa [coordinateSignature, offset] using h₀
  · apply Prod.ext
    · have h₁ := congrArg Syllable.exponent (h 1)
      simpa [coordinateSignature, offset] using h₁
    · have h₂ := congrArg Syllable.exponent (h 2)
      simpa [coordinateSignature, offset] using h₂

/-- The same triple also recovers both ordinary factor labels. -/
theorem triple_determines_row {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u r' u' : Fin d) (a b : Rotation)
    (h : ∀ t : Fin 3,
      syllable z r u a.1 a.2.1 (offset a.2.2 t) =
        syllable z r' u' b.1 b.2.1 (offset b.2.2 t)) :
    r = r' ∧ u = u' ∧ a = b := by
  have hab := triple_determines_rotation z r u r' u' a b h
  subst b
  obtain ⟨tx, hx⟩ := triple_contains_x a
  obtain ⟨ty, hy⟩ := triple_contains_y a
  have hcx : orientedCoordinate a.1 a.2.1 (offset a.2.2 tx) ≠ 0 := by
    intro hzero
    simp [hzero] at hx
  have hcy : orientedCoordinate a.1 a.2.1 (offset a.2.2 ty) ≠ 0 := by
    intro hzero
    simp [hzero] at hy
  have hny : (orientedCoordinate a.1 a.2.1 (offset a.2.2 ty)).natAbs ≠ 1 := by omega
  have hhx := h tx
  have hhy := h ty
  simp only [syllable, ite_eq_right hcx, ite_eq_left hx, Syllable.ordinary.injEq] at hhx
  simp only [syllable, ite_eq_right hcy, ite_eq_right hny, Syllable.ordinary.injEq] at hhy
  exact ⟨hhx.1, hhy.1, rfl⟩

def category (j : Fin 2) (forward : Bool) (p : Fin 33) : Fin 3 :=
  let c := orientedCoordinate j forward p
  if c = 0 then 0 else if c.natAbs = 1 then 1 else 2

set_option maxRecDepth 10000 in
theorem category_adjacent_ne :
    ∀ (j : Fin 2) (b : Bool) (p : Fin 33), category j b p ≠ category j b (p + 1) := by
  decide

def factorOfCategory {d : ℕ} (r u : Fin d) (c : Fin 3) : (Fin d × Fin d) ⊕ Fin d :=
  if c = 0 then .inl (r, u) else if c = 1 then .inr r else .inr u

theorem factorOfCategory_injective {d : ℕ} (r u : Fin d) (hru : r ≠ u) :
    Function.Injective (factorOfCategory r u) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [factorOfCategory]

theorem syllable_factor {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (b : Bool) (p : Fin 33) :
    (syllable z r u j b p).factor = factorOfCategory r u (category j b p) := by
  simp only [syllable, category]
  split
  · simp [Syllable.factor, factorOfCategory]
  · split <;> simp [Syllable.factor, factorOfCategory]

/-- The indexed row is cyclically reduced: every adjacent pair, including the wrap, differs
in its free-product factor. -/
theorem syllable_cyclically_reduced {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (hru : r ≠ u) (j : Fin 2) (b : Bool) (p : Fin 33) :
    (syllable z r u j b p).factor ≠ (syllable z r u j b (p + 1)).factor := by
  rw [syllable_factor, syllable_factor]
  exact fun h ↦ category_adjacent_ne j b p (factorOfCategory_injective r u hru h)

/-- A cyclic shift preserving the row must be the zero shift, excluding proper powers. -/
theorem syllable_aperiodic {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (b : Bool) (s : Fin 33)
    (h : ∀ p, syllable z r u j b (p + s) = syllable z r u j b p) : s = 0 := by
  have heq : (j, b, s) = (j, b, (0 : Fin 33)) := by
    apply triple_determines_rotation z r u r u
    intro t
    change syllable z r u j b (s + ⟨t.val, by omega⟩) =
      syllable z r u j b (0 + ⟨t.val, by omega⟩)
    rw [Fin.zero_add]
    have hcomm : s + (⟨t.val, by omega⟩ : Fin 33) = ⟨t.val, by omega⟩ + s := by
      apply Fin.ext
      simp [Fin.add_def, Nat.add_comm]
    rw [hcomm]
    exact h _
  exact congrArg (fun a : Rotation ↦ a.2.2) heq

theorem noncyclic_not_both_zpowers {L : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (z : Q.Group) :
    ¬ (PresentedGroup.of (rels := Q.relSet) 0 ∈ Subgroup.zpowers z ∧
      PresentedGroup.of (rels := Q.relSet) 1 ∈ Subgroup.zpowers z) := by
  intro hz
  apply hQ
  refine ⟨z, fun x ↦ Subgroup.mem_zpowers_iff.mp ?_⟩
  apply PresentedGroup.generated_by Q.relSet (Subgroup.zpowers z) _ x
  intro i
  fin_cases i
  · exact hz.1
  · exact hz.2

theorem noncyclic_generator_ne_one {L : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group)
    (i : Fin 2) : PresentedGroup.of (rels := Q.relSet) i ≠ 1 := by
  fin_cases i
  · intro h
    change PresentedGroup.of (rels := Q.relSet) 0 = 1 at h
    apply noncyclic_not_both_zpowers Q hQ (PresentedGroup.of 1)
    constructor
    · rw [h]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  · intro h
    change PresentedGroup.of (rels := Q.relSet) 1 = 1 at h
    apply noncyclic_not_both_zpowers Q hQ (PresentedGroup.of 0)
    constructor
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · rw [h]
      exact Subgroup.one_mem _

theorem noncyclic_generators_distinct {L : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group) :
    PresentedGroup.of (rels := Q.relSet) 0 ≠ PresentedGroup.of 1 := by
  intro h
  apply noncyclic_not_both_zpowers Q hQ (PresentedGroup.of 0)
  constructor
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simpa using h⟩

theorem noncyclic_generators_not_inverse {L : ℕ} (Q : FP 2 L) (hQ : Noncyclic Q.Group) :
    PresentedGroup.of (rels := Q.relSet) 0 ≠ (PresentedGroup.of 1)⁻¹ := by
  intro h
  apply noncyclic_not_both_zpowers Q hQ (PresentedGroup.of 1)
  constructor
  · exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simpa using h.symm⟩
  · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

def syllableRow {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (b : Bool) : List (Syllable G d) :=
  List.ofFn (syllable z r u j b)

@[simp] theorem syllableRow_length {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) (b : Bool) : (syllableRow z r u j b).length = 33 := by
  simp [syllableRow]

/-- The finite signed exponent lists used by the two actual source words. -/
def codePowers (j : Fin 2) : List ℤ :=
  if j = 0 then (List.range' 2 15).map Int.ofNat ++ [-150]
  else (List.range' 17 15).map Int.ofNat ++ [-376]

set_option maxRecDepth 10000 in
theorem syllableRow_literal {G : Type*} [Group G] {d : ℕ} (z : Fin 2 → G)
    (r u : Fin d) (j : Fin 2) :
    syllableRow z r u j true =
      .special r u (z j)⁻¹ :: (codePowers j).flatMap
        (fun q ↦ [.ordinary r 1, .ordinary u q]) := by
  fin_cases j <;> rfl

end SmallPresentationStatements.SignedCoding
