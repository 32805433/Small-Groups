module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! Metric semi-initial pieces and indexed free-product presentations.
These definitions and all overlap/counting lemmas are independent of the
geometric reduction theorems. -/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]

abbrev Syllable := Σ a, G a

structure Origin where
  row : I
  forward : Bool
  position : Fin (length row)

def inverseSyllable (s : Syllable G) : Syllable G := ⟨s.1, s.2⁻¹⟩

def oriented (rows : ∀ i, Fin (length i) → Syllable G)
    (i : I) (forward : Bool) (p : Fin (length i)) : Syllable G :=
  if forward then rows i p else inverseSyllable G (rows i (-p))

def syllableAt (rows : ∀ i, Fin (length i) → Syllable G) (a : Origin length) (t : ℕ) : Syllable G :=
  oriented G length rows a.row a.forward (a.position + Fin.ofNat (length a.row) t)

def TripleInjective (rows : ∀ i, Fin (length i) → Syllable G) : Prop :=
  ∀ a b : Origin length, (∀ t : Fin 3, syllableAt G length rows a t.val = syllableAt G length rows b t.val) → a = b

/-- The exact semi-initial condition: all but the final syllable agree, and the
final syllables lie in the same factor. -/
def SemiInitial (rows : ∀ i, Fin (length i) → Syllable G)
    (a b : Origin length) (m : ℕ) : Prop :=
  0 < m ∧ m ≤ length a.row ∧ m ≤ length b.row ∧
    (∀ t < m - 1, syllableAt G length rows a t = syllableAt G length rows b t) ∧
    (syllableAt G length rows a (m - 1)).1 = (syllableAt G length rows b (m - 1)).1

def Piece (rows : ∀ i, Fin (length i) → Syllable G) (a : Origin length) (m : ℕ) : Prop :=
  ∃ b, b ≠ a ∧ SemiInitial G length rows a b m

theorem piece_length_le_three (rows : ∀ i, Fin (length i) → Syllable G)
    (h : TripleInjective G length rows) (a : Origin length) (m : ℕ)
    (hm : Piece G length rows a m) : m ≤ 3 := by
  obtain ⟨b, hba, hb⟩ := hm
  by_contra hn
  apply hba
  symm
  apply h a b
  intro t
  exact hb.2.2.2.1 t.val (by omega)

/-- The metric `C′(1/6)` condition for semi-initial free-product pieces. Unlike
triple injectivity, this condition allows arbitrary piece lengths and relator lengths. -/
def MetricSmallCancellation (rows : ∀ i, Fin (length i) → Syllable G) : Prop :=
  ∀ a m, Piece G length rows a m → 6 * m < length a.row

/-- The concrete triple certificate implies the general metric overlap condition. -/
theorem metric_of_triple_injective (rows : ∀ i, Fin (length i) → Syllable G)
    (h : TripleInjective G length rows) (hlength : ∀ i, 19 ≤ length i) :
    MetricSmallCancellation G length rows := by
  intro a m hm
  have hp := piece_length_le_three G length rows h a m hm
  have hl := hlength a.row
  omega

/-- A parameterized piece bound yields metric small cancellation whenever six
pieces of maximal length are still shorter than every relator. -/
theorem metric_of_uniform_piece_bound (rows : ∀ i, Fin (length i) → Syllable G)
    (k : ℕ) (hbound : ∀ a m, Piece G length rows a m → m ≤ k)
    (hlength : ∀ i, 6 * k < length i) : MetricSmallCancellation G length rows := by
  intro a m hm
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 6 (hbound a m hm)) (hlength a.row)

/-- Metric small cancellation excludes repeated oriented origins, including a
nontrivial period of a relator or an inverse-cyclic coincidence. -/
theorem origin_eq_of_full_overlap (rows : ∀ i, Fin (length i) → Syllable G)
    (hmetric : MetricSmallCancellation G length rows) (a b : Origin length)
    (hlen : length a.row ≤ length b.row)
    (heq : ∀ t < length a.row, syllableAt G length rows a t =
      syllableAt G length rows b t) : a = b := by
  by_contra hab
  have hpos : 0 < length a.row := Fin.pos a.position
  have hp : Piece G length rows a (length a.row) := by
    refine ⟨b, Ne.symm hab, hpos, le_rfl, hlen, ?_, ?_⟩
    · intro t ht
      exact heq t (by omega)
    · exact congrArg Sigma.fst (heq (length a.row - 1) (by omega))
  have h := hmetric a (length a.row) hp
  omega

/-- Every factorization of a relator into actual semi-initial pieces has at least
seven factors under the strict metric condition, hence satisfies generalized C(6). -/
theorem at_least_seven_pieces_of_metric (rows : ∀ i, Fin (length i) → Syllable G)
    (hmetric : MetricSmallCancellation G length rows) (a : Origin length)
    (ms : List ℕ) (hsum : ms.sum = length a.row)
    (hpieces : ∀ m ∈ ms, ∃ b : Origin length,
      b.row = a.row ∧ Piece G length rows b m) : 7 ≤ ms.length := by
  have hpos : 0 < length a.row := Fin.pos a.position
  have hbound : ∀ m ∈ ms, 6 * m ≤ length a.row - 1 := by
    intro m hm
    obtain ⟨b, hrow, hp⟩ := hpieces m hm
    have h := hmetric b m hp
    rw [hrow] at h
    omega
  have hb : 6 * ms.sum ≤ (length a.row - 1) * ms.length := by
    clear hpieces hsum
    induction ms with
    | nil => simp
    | cons m ms ih =>
      have hm := hbound m (by simp)
      have ht := ih (fun n hn ↦ hbound n (by simp [hn]))
      simp only [List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_succ]
      omega
  by_contra hn
  have hn' : ms.length ≤ 6 := by omega
  have hmul := Nat.mul_le_mul_left (length a.row - 1) hn'
  rw [hsum] at hb
  omega

private theorem sum_le_three_mul_length (ms : List ℕ) (h : ∀ m ∈ ms, m ≤ 3) :
    ms.sum ≤ 3 * ms.length := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    have hm := h m (by simp)
    have hms := ih (fun n hn ↦ h n (by simp [hn]))
    simp only [List.sum_cons, List.length_cons]
    omega

/-- Every actual factorization into semi-initial pieces satisfies this stronger
count estimate; positions of the pieces are immaterial once their lengths are bounded. -/
theorem piece_count_bound (rows : ∀ i, Fin (length i) → Syllable G)
    (h : TripleInjective G length rows) (a : Origin length) (ms : List ℕ)
    (hsum : ms.sum = length a.row)
    (hpieces : ∀ m ∈ ms, ∃ b, Piece G length rows b m) :
    length a.row ≤ 3 * ms.length := by
  rw [← hsum]
  apply sum_le_three_mul_length
  intro m hm
  obtain ⟨b, hb⟩ := hpieces m hm
  exact piece_length_le_three G length rows h b m hb

theorem at_least_six_pieces (rows : ∀ i, Fin (length i) → Syllable G)
    (h : TripleInjective G length rows) (hlength : ∀ i, 19 ≤ length i)
    (a : Origin length) (ms : List ℕ) (hsum : ms.sum = length a.row)
    (hpieces : ∀ m ∈ ms, ∃ b, Piece G length rows b m) : 6 ≤ ms.length := by
  have hb := piece_count_bound G length rows h a ms hsum hpieces
  have hl := hlength a.row
  omega

/-- Interpret a syllable in the indexed free product. -/
def includeSyllable (s : Syllable G) : Monoid.CoprodI G := Monoid.CoprodI.of s.2

def relatorValue (rows : ∀ i, Fin (length i) → Syllable G) (i : I) : Monoid.CoprodI G :=
  (List.ofFn fun p ↦ includeSyllable G (rows i p)).prod

abbrev relatorSubgroup (rows : ∀ i, Fin (length i) → Syllable G) :=
  Subgroup.normalClosure (Set.range (relatorValue G length rows))

abbrev Quotient (rows : ∀ i, Fin (length i) → Syllable G) :=
  Monoid.CoprodI G ⧸ relatorSubgroup G length rows

def factorMap (rows : ∀ i, Fin (length i) → Syllable G) (a : A) :
    G a →* Quotient G length rows :=
  (QuotientGroup.mk' (relatorSubgroup G length rows)).comp Monoid.CoprodI.of

end SmallPresentationStatements.RelativeSmallCancellation
