module

public import SmallPresentation.UniversalGroup.Coding.Thue.PriorityStage

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/PriorityStage.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.FinalStage
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Priority

/-!
The power-of-two padding, transposition, and first priority block from
Sections 2.3--2.4 of Matiyasevich (1995).  This file is deliberately
parameterized by the binary rule words; the preceding binary encoding stage
supplies those words and their common-length/code-language properties.
-/
/-- The exponent `u` for the least power `t = 2^u` not below `r`. -/
def exponent (r : ℕ) : ℕ := Nat.clog 2 r

/-- The number `t` of rows used in the transposed long relation. -/
def powerCount (r : ℕ) : ℕ := 2 ^ exponent r

theorem relationCount_le_powerCount (r : ℕ) : r ≤ powerCount r :=
  (Nat.clog_le_iff_le_pow (b := 2) (by omega)).mp le_rfl

theorem powerCount_pos (r : ℕ) : 0 < powerCount r :=
  pow_pos (by omega) _

/-- Repeat the first relation when the original list is extended to `2^u`
relations.  The paper repeats the last relation; either choice has the same
effect. -/
def paddedIndex {r : ℕ} (hr : 0 < r) (i : Fin (powerCount r)) : Fin r :=
  if h : i.val < r then ⟨i.val, h⟩ else ⟨0, hr⟩

def paddedSide {r : ℕ} (hr : 0 < r) {α : Type*}
    (W : Fin r → List α) (i : Fin (powerCount r)) : List α :=
  W (paddedIndex hr i)

/-- Equation (11) for `i=1`: append `a e^u` to the binary encoding. -/
def encode (u : ℕ) (W : List (Fin 2)) : List A₂ :=
  liftBinary W ++ [a] ++ List.replicate u e

theorem encode_computable (u : ℕ) : Computable (encode u) := by
  have hlift : Primrec liftBinary :=
    list_map_primrec_of_finite liftBit
  have hwithA : Primrec fun W : List (Fin 2) => liftBinary W ++ [a] :=
    Primrec.list_append.comp hlift (Primrec.const [a])
  exact (Primrec.list_append.comp hwithA
    (Primrec.const (List.replicate u e))).to_comp

theorem encode_ne_nil (u : ℕ) (W : List (Fin 2)) : encode u W ≠ [] := by
  simp [encode]

@[simp] theorem encode_eCount (u : ℕ) (W : List (Fin 2)) :
    eCount (encode u W) = u := by
  rw [show encode u W =
    liftBinary W ++ ([a] ++ List.replicate u e) by simp [encode]]
  rw [eCount_append, eCount_liftBinary]
  simp [eCount, a, e]

@[simp] theorem firstNormal_encode (u : ℕ) (W : List (Fin 2)) :
    firstNormal (encode u W) = encode u W := by
  unfold encode
  rw [List.append_assoc]
  rw [firstNormal_liftBinary_append]
  simp only [List.singleton_append, firstNormal_a_cons,
    firstNormal_replicate_e]

theorem stage₂_side_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) (i : Fin 5) :
    eCount (stage₂F L i) = eCount (stage₂E M i) := by
  fin_cases i
  · change List.count (2 : Fin 3) [2, 0, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 0, 1] = List.count 2 [1, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 0] = List.count 2 [0, 2]
    decide
  · change List.count (2 : Fin 3) [2, 1, 1] = List.count 2 [1, 2]
    decide
  · change eCount L = eCount M
    exact hLM

theorem stage₂Step_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueStep (stage₂System L M) X Y) : eCount X = eCount Y := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hwords⟩
  injection hxy with hx hy
  subst x
  subst y
  have hsides := stage₂_side_eCount L M hLM i
  rcases hwords with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [eCount, Nat.add_assoc] using
      congrArg (fun n => eCount l + n + eCount r) hsides
  · simpa [eCount, Nat.add_assoc] using
      (congrArg (fun n => eCount l + n + eCount r) hsides).symm

theorem stage₂Eq_eCount (L M : List A₂)
    (hLM : eCount L = eCount M) {X Y : List A₂}
    (h : ThueEq (stage₂System L M) X Y) : eCount X = eCount Y := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (stage₂Step_eCount L M hLM hstep)

/-- The invariant furnished by equation (25): every reachable first priority
normal form remains in the binary code language and hence has no `aaa`. -/
def ReachableNoAAA (L M X : List A₂) : Prop :=
  ∀ W, ThueEq (stage₂System L M) X W → NoAAA (firstNormal W)

/-- The exact shape needed from the transposed words: the initial `2t` copies
of `a` and a final `b`. -/
def LongShape (run : ℕ) (W : List A₂) : Prop :=
  ∃ middle, W = List.replicate run a ++ middle ++ [b]

/-- Decode a long side with a residual `d` inside arbitrary contexts. -/
theorem phi₂_residual_long_context {run : ℕ} {W : List A₂}
    (hshape : LongShape run W) (l : List (Fin 2)) (R : List A₂) :
    ∃ middle,
      phi₂ (l ++ rho₂ W ++ (0 : Fin 2) :: rho₂ R) =
        phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
  obtain ⟨middle, rfl⟩ := hshape
  refine ⟨middle, ?_⟩
  have hblock :
      rho₂ (List.replicate run a ++ middle ++ [b]) ++ [(0 : Fin 2)] =
      rho₂ (List.replicate run a ++ middle ++ [a, e]) := by
    simp [rho₂, rho₂Letter, a, b, e, List.append_assoc]
  calc
    phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [b]) ++
        (0 : Fin 2) :: rho₂ R) =
        phi₂ (l ++ (rho₂ (List.replicate run a ++ middle ++ [b]) ++
          [(0 : Fin 2)]) ++ rho₂ R) := by
          simp only [List.append_assoc, List.singleton_append]
    _ = phi₂ (l ++ rho₂ (List.replicate run a ++ middle ++ [a, e]) ++
          rho₂ R) := by rw [hblock]
    _ = phi₂ l ++ (List.replicate run a ++ middle ++ [a, e]) ++ R :=
      phi₂_context_rho₂ l _ R
    _ = phi₂ l ++ List.replicate run a ++ middle ++ [a, e] ++ R := by
      simp only [List.append_assoc]

/-! ### Excluding the residual decoder alignment -/

/-- If the two invariants isolated on page 50 hold, then an occurrence of
the long final relation cannot be followed by the residual unmatched `d`.
This is the counting core of the converse `T₃ → T₂`: the initial run of
`a`'s forces all `u` priority letters into the left context, while decoding
the residual `d` creates one additional `e`. -/
theorem long_aligned_of_decoded_reachable {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hdecode : ThueEq (stage₂System L M) X (phi₂ W)) :
    ∀ l r,
      (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r := by
  intro l r hocc
  rcases rho₂_phi₂_reconstruct r with hexact | hresidual
  · exact hexact
  · have hnormal : NoAAA (firstNormal (phi₂ W)) :=
      hNoAAA (phi₂ W) hdecode
    have hform : ∃ middle,
        phi₂ W = phi₂ l ++ List.replicate run a ++
          middle ++ [a, e] ++ phi₂ r := by
      rcases hocc with hocc | hocc
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeL l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ L ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ L ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
      · obtain ⟨middle, hmiddle⟩ :=
          phi₂_residual_long_context hshapeM l (phi₂ r)
        refine ⟨middle, ?_⟩
        calc
          phi₂ W = phi₂ (l ++ rho₂ M ++ r) := congrArg phi₂ hocc
          _ = phi₂ (l ++ rho₂ M ++
              (0 : Fin 2) :: rho₂ (phi₂ r)) := by rw [hresidual]
          _ = _ := hmiddle
    obtain ⟨middle, hform⟩ := hform
    rw [hform] at hnormal
    have hleft : u ≤ eCount (phi₂ l) := by
      apply hRun (phi₂ l) (middle ++ [a, e] ++ phi₂ r)
      simpa only [List.append_assoc] using hnormal
    have hcount := stage₂Eq_eCount L M hLM hdecode
    rw [hX, hform] at hcount
    simp only [eCount_append, eCount_replicate_a, eCount_ae,
      Nat.add_zero] at hcount
    omega

/-- Simultaneously decode a final-system derivation and establish the
alignment invariant required for its next long-rule step.  The simultaneous
induction avoids any circularity: alignment at the current word decodes the
next step, and the decoded prefix derivation re-establishes alignment at the
new word by `long_aligned_of_decoded_reachable`. -/
theorem final_decode_and_aligned {u run : ℕ}
    {L M X : List A₂} {W : List (Fin 2)}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M)
    (hfinal : ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W) :
    ThueEq (stage₂System L M) X (phi₂ W) ∧
      ∀ l r,
        (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
        rho₂ (phi₂ r) = r := by
  induction hfinal with
  | refl =>
      have hdecode :
          ThueEq (stage₂System L M) X (phi₂ (rho₂ X)) := by
        rw [phi₂_rho₂]
        exact Relation.ReflTransGen.refl
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩
  | tail hab hbc ih =>
      have hstep : ThueEq (stage₂System L M) (phi₂ _) (phi₂ _) :=
        phi₂_step_of_long_aligned L M ih.2 hbc
      have hdecode := ih.1.trans hstep
      exact ⟨hdecode, long_aligned_of_decoded_reachable hLM hX hNoAAA
        hRun hshapeL hshapeM hdecode⟩

/-- The page-50 invariants imply the exact alignment predicate consumed by
the final-stage reflection theorem. -/
theorem longRuleAlignedFrom_of_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) :
    LongRuleAlignedFrom L M X := by
  intro W hfinal
  exact (final_decode_and_aligned hLM hX hNoAAA hRun
    hshapeL hshapeM hfinal).2

/-- A convenient conditional form of equivalence (10), with the two
priority invariants made explicit. -/
theorem rho₂_iff_of_priority_invariants {u run : ℕ}
    {L M X : List A₂}
    (hLM : eCount L = eCount M)
    (hX : eCount X = u)
    (hNoAAA : ReachableNoAAA L M X)
    (hRun : LongRunRequirement u run)
    (hshapeL : LongShape run L)
    (hshapeM : LongShape run M) (Y : List A₂) :
    ThueEq (stage₂System L M) X Y ↔
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  apply rho₂_iff_of_longRuleAligned
  exact longRuleAlignedFrom_of_invariants hLM hX hNoAAA hRun
    hshapeL hshapeM

end Priority
end Matiyasevich1993
end Thue
end UniversalGroup
