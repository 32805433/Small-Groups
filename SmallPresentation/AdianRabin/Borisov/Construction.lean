module

/-
Ported from `GroupUndecidability/Borisov/Construction.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.StandingDatum
public import SmallPresentation.UniversalGroup.Simulator.Recognition.Forward

@[expose] public section

namespace UniversalGroup
namespace Borisov

open SimulatorRecognitionForward (evalPositive_append evalPositive_commute d_transport
  e_transport pack_context conjugate_context)

theorem inverse_commutator_eq_one_iff {G : Type*} [Group G]
    (a b : G) :
    a⁻¹ * b⁻¹ * a * b = 1 ↔ a * b = b * a := by
  change a⁻¹ * b⁻¹ * a * b = 1 ↔ Commute a b
  simpa only [commutatorElement_def, inv_inv, Commute.inv_inv_iff] using
    (commutatorElement_eq_one_iff_commute (g₁ := a⁻¹) (g₂ := b⁻¹))

theorem commute_of_inverse_commutator_eq_one {G : Type*} [Group G]
    {a b : G} (h : a⁻¹ * b⁻¹ * a * b = 1) :
    Commute a b :=
  (inverse_commutator_eq_one_iff a b).mp h

theorem commute_conjugate_iff_of_commute {G : Type*} [Group G]
    {g x k : G} (hgk : Commute g k) :
    Commute (g * x * g⁻¹) k ↔ Commute x k := by
  simpa only [hgk.mul_inv_cancel] using
    (Commute.conj_iff (a := x) (b := k) g)

theorem test_conjugate_repack {G : Type*} [Group G]
    (d e t q : G) (I J : ℕ) (htd : Commute t d) :
    e ^ J * ((d ^ I * q * e ^ J)⁻¹ * t * (d ^ I * q * e ^ J)) *
          (e ^ J)⁻¹ =
      q⁻¹ * t * q := by
  have hdt : (d ^ I)⁻¹ * t * d ^ I = t :=
    (htd.pow_right I).symm.inv_mul_cancel
  simp [mul_inv_rev, mul_assoc]
  simpa only [mul_assoc] using congrArg (fun x => x * q) hdt

theorem test_repack_commute_iff {G : Type*} [Group G]
    (d e t k q : G) (I J : ℕ) (htd : Commute t d)
    (hke : Commute k e) :
    Commute (q⁻¹ * t * q) k ↔
      Commute ((d ^ I * q * e ^ J)⁻¹ * t * (d ^ I * q * e ^ J)) k := by
  rw [← test_conjugate_repack d e t q I J htd]
  exact commute_conjugate_iff_of_commute (hke.symm.pow_left J)

theorem simulation_conjugate {G : Type*} [Group G]
    (c t A B : G) (hAB : c⁻¹ * A * c = B) (htc : Commute t c) :
    B⁻¹ * t * B = c⁻¹ * (A⁻¹ * t * A) * c := by
  rw [← hAB]
  have hct : c * t * c⁻¹ = t := htc.symm.mul_inv_cancel
  have hh := congrArg (fun x => c⁻¹ * A⁻¹ * x * A * c) hct
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh

theorem simulation_preserves_commute {G : Type*} [Group G]
    (c t k A B : G) (hAB : c⁻¹ * A * c = B)
    (htc : Commute t c) (hkc : Commute k c) :
    Commute (A⁻¹ * t * A) k ↔ Commute (B⁻¹ * t * B) k := by
  have hck : Commute c⁻¹ k := Commute.inv_left_iff.mpr hkc.symm
  rw [simulation_conjugate c t A B hAB htc]
  simpa only [inv_inv] using
    (commute_conjugate_iff_of_commute
      (g := c⁻¹) (x := A⁻¹ * t * A) (k := k) hck).symm

abbrev BorisovWord := Word 7

/-- Generator order: `d,e,s₁,s₂,c,t,k`. -/
def dWord : BorisovWord := Word.generator 0
def eWord : BorisovWord := Word.generator 1
def s1Word : BorisovWord := Word.generator 2
def s2Word : BorisovWord := Word.generator 3
def cWord : BorisovWord := Word.generator 4
def tWord : BorisovWord := Word.generator 5
def kWord : BorisovWord := Word.generator 6

def positiveWord (w : List (Fin 2)) : BorisovWord :=
  Word.substitutePositive s1Word s2Word w

def s_d_relator (s : BorisovWord) : BorisovWord :=
  Word.relation
    (Word.product [Word.inverse s, Word.pow dWord 4, s])
    dWord

def s_e_relator (s : BorisovWord) : BorisovWord :=
  Word.relation
    (Word.product [Word.inverse s, eWord, s])
    (Word.pow eWord 4)

def simulationRelator
    (datum : Thue.StandingDatum) (i : Fin 3) : BorisovWord :=
  let exponent := i.val + 1
  Word.relation
    (Word.product
      [Word.inverse cWord, Word.pow dWord exponent,
       positiveWord (datum.F i), Word.pow eWord exponent, cWord])
    (Word.product
      [Word.pow dWord exponent, positiveWord (datum.E i),
       Word.pow eWord exponent])

def pWord (datum : Thue.StandingDatum) : BorisovWord :=
  let P := positiveWord datum.P
  Word.product [Word.inverse P, tWord, P]

/-- Borisov's seven-generator, fourteen-relator simulator `Gamma`. -/
def presentation (datum : Thue.StandingDatum) : FP 7 14 where
  relator := ![
    s_d_relator s1Word,
    s_e_relator s1Word,
    s_d_relator s2Word,
    s_e_relator s2Word,
    Word.commutator s1Word cWord,
    Word.commutator s2Word cWord,
    simulationRelator datum 0,
    simulationRelator datum 1,
    simulationRelator datum 2,
    Word.commutator tWord cWord,
    Word.commutator tWord dWord,
    Word.commutator kWord cWord,
    Word.commutator kWord eWord,
    Word.commutator kWord (pWord datum)
  ]

/-- Borisov's test word `[Q⁻¹tQ,k]`. -/
def testWord (Q : List (Fin 2)) : BorisovWord :=
  let q := positiveWord Q
  Word.commutator
    (Word.product [Word.inverse q, tWord, q])
    kWord

theorem relation_of_relator (P : FP n m) (i : Fin m)
    (lhs rhs : Word n) (hi : P.relator i = Word.relation lhs rhs) :
    P.evalWord lhs = P.evalWord rhs := by
  have h := P.relator_eq_one i
  rw [hi] at h
  change Word.eval (fun j => PresentedGroup.of j) (Word.relation lhs rhs) = 1 at h
  exact (Word.eval_relation_eq_one_iff _ lhs rhs).mp h

@[simp]
theorem eval_positiveWord {G : Type*} [Group G]
    (x : Fin 7 → G) (w : List (Fin 2)) :
    Word.eval x (positiveWord w) = UniversalGroup.evalPositive (x 2) (x 3) w := by
  simp [positiveWord, UniversalGroup.evalPositive, s1Word, s2Word]

abbrev gen (datum : Thue.StandingDatum) (i : Fin 7) :
    (presentation datum).Group :=
  PresentedGroup.of i

theorem presented_relation (datum : Thue.StandingDatum) (i : Fin 14)
    (lhs rhs : BorisovWord)
    (hi : (presentation datum).relator i = Word.relation lhs rhs) :
    Word.eval (gen datum) lhs = Word.eval (gen datum) rhs := by
  simpa [FP.evalWord] using
    relation_of_relator (presentation datum) i lhs rhs hi

theorem d_letter_relations (datum : Thue.StandingDatum) :
    let d := gen datum 0
    let s₁ := gen datum 2
    let s₂ := gen datum 3
    d ^ 4 * s₁ = s₁ * d ∧ d ^ 4 * s₂ = s₂ * d := by
  dsimp only
  have h₁ := presented_relation datum 0
    (Word.product [Word.inverse s1Word, Word.pow dWord 4, s1Word]) dWord
    (by simp [presentation, s_d_relator])
  have h₂ := presented_relation datum 2
    (Word.product [Word.inverse s2Word, Word.pow dWord 4, s2Word]) dWord
    (by simp [presentation, s_d_relator])
  have h₁' : (gen datum 2)⁻¹ * (gen datum 0) ^ 4 * gen datum 2 = gen datum 0 := by
    simpa [dWord, s1Word, mul_assoc] using h₁
  have h₂' : (gen datum 3)⁻¹ * (gen datum 0) ^ 4 * gen datum 3 = gen datum 0 := by
    simpa [dWord, s2Word, mul_assoc] using h₂
  constructor
  · calc
      (gen datum 0) ^ 4 * gen datum 2 =
          gen datum 2 * ((gen datum 2)⁻¹ * (gen datum 0) ^ 4 * gen datum 2) := by
            simp [mul_assoc]
      _ = gen datum 2 * gen datum 0 := by rw [h₁']
  · calc
      (gen datum 0) ^ 4 * gen datum 3 =
          gen datum 3 * ((gen datum 3)⁻¹ * (gen datum 0) ^ 4 * gen datum 3) := by
            simp [mul_assoc]
      _ = gen datum 3 * gen datum 0 := by rw [h₂']

theorem e_letter_relations (datum : Thue.StandingDatum) :
    let e := gen datum 1
    let s₁ := gen datum 2
    let s₂ := gen datum 3
    e * s₁ = s₁ * e ^ 4 ∧ e * s₂ = s₂ * e ^ 4 := by
  dsimp only
  have h₁ := presented_relation datum 1
    (Word.product [Word.inverse s1Word, eWord, s1Word]) (Word.pow eWord 4)
    (by simp [presentation, s_e_relator])
  have h₂ := presented_relation datum 3
    (Word.product [Word.inverse s2Word, eWord, s2Word]) (Word.pow eWord 4)
    (by simp [presentation, s_e_relator])
  have h₁' : (gen datum 2)⁻¹ * gen datum 1 * gen datum 2 =
      (gen datum 1) ^ 4 := by
    simpa [eWord, s1Word, mul_assoc] using h₁
  have h₂' : (gen datum 3)⁻¹ * gen datum 1 * gen datum 3 =
      (gen datum 1) ^ 4 := by
    simpa [eWord, s2Word, mul_assoc] using h₂
  constructor
  · calc
      gen datum 1 * gen datum 2 =
          gen datum 2 * ((gen datum 2)⁻¹ * gen datum 1 * gen datum 2) := by
            simp [mul_assoc]
      _ = gen datum 2 * (gen datum 1) ^ 4 := by rw [h₁']
  · calc
      gen datum 1 * gen datum 3 =
          gen datum 3 * ((gen datum 3)⁻¹ * gen datum 1 * gen datum 3) := by
            simp [mul_assoc]
      _ = gen datum 3 * (gen datum 1) ^ 4 := by rw [h₂']

theorem presented_relator_eq_one (datum : Thue.StandingDatum)
    (i : Fin 14) :
    Word.eval (gen datum) ((presentation datum).relator i) = 1 := by
  simpa [FP.evalWord] using (presentation datum).relator_eq_one i

theorem c_letter_relations (datum : Thue.StandingDatum) :
    Commute (gen datum 2) (gen datum 4) ∧
      Commute (gen datum 3) (gen datum 4) := by
  have h₁ := presented_relator_eq_one datum 4
  have h₂ := presented_relator_eq_one datum 5
  have hr₁ : (presentation datum).relator 4 =
      Word.commutator s1Word cWord := by simp [presentation]
  have hr₂ : (presentation datum).relator 5 =
      Word.commutator s2Word cWord := by simp [presentation]
  rw [hr₁] at h₁
  rw [hr₂] at h₂
  have h₁' : (gen datum 2)⁻¹ * (gen datum 4)⁻¹ *
      gen datum 2 * gen datum 4 = 1 := by
    simpa only [Word.eval_commutator, s1Word, cWord,
      Word.eval_generator, ← mul_assoc] using h₁
  have h₂' : (gen datum 3)⁻¹ * (gen datum 4)⁻¹ *
      gen datum 3 * gen datum 4 = 1 := by
    simpa only [Word.eval_commutator, s2Word, cWord,
      Word.eval_generator, ← mul_assoc] using h₂
  exact ⟨commute_of_inverse_commutator_eq_one h₁',
    commute_of_inverse_commutator_eq_one h₂'⟩

theorem fixed_commutations (datum : Thue.StandingDatum) :
    Commute (gen datum 5) (gen datum 4) ∧
    Commute (gen datum 5) (gen datum 0) ∧
    Commute (gen datum 6) (gen datum 4) ∧
    Commute (gen datum 6) (gen datum 1) := by
  have htc := presented_relator_eq_one datum 9
  have htd := presented_relator_eq_one datum 10
  have hkc := presented_relator_eq_one datum 11
  have hke := presented_relator_eq_one datum 12
  simp only [presentation] at htc htd hkc hke
  simp only [tWord, cWord, dWord, kWord, eWord] at htc htd hkc hke
  exact ⟨commute_of_inverse_commutator_eq_one htc,
    commute_of_inverse_commutator_eq_one htd,
    commute_of_inverse_commutator_eq_one hkc,
    commute_of_inverse_commutator_eq_one hke⟩

theorem simulation_relation_semantic (datum : Thue.StandingDatum)
    (i : Fin 3) :
    let exponent := i.val + 1
    let d := gen datum 0
    let e := gen datum 1
    let s₁ := gen datum 2
    let s₂ := gen datum 3
    let c := gen datum 4
    c⁻¹ * d ^ exponent * UniversalGroup.evalPositive s₁ s₂ (datum.F i) *
        e ^ exponent * c =
      d ^ exponent * UniversalGroup.evalPositive s₁ s₂ (datum.E i) *
        e ^ exponent := by
  dsimp only
  fin_cases i
  · have h := presented_relation datum 6
      (Word.product [Word.inverse cWord, Word.pow dWord 1,
        positiveWord (datum.F 0), Word.pow eWord 1, cWord])
      (Word.product [Word.pow dWord 1, positiveWord (datum.E 0),
        Word.pow eWord 1])
      (by simp [presentation, simulationRelator])
    simpa [dWord, eWord, cWord, mul_assoc] using h
  · have h := presented_relation datum 7
      (Word.product [Word.inverse cWord, Word.pow dWord 2,
        positiveWord (datum.F 1), Word.pow eWord 2, cWord])
      (Word.product [Word.pow dWord 2, positiveWord (datum.E 1),
        Word.pow eWord 2])
      (by simp [presentation, simulationRelator])
    simpa [dWord, eWord, cWord, mul_assoc] using h
  · have h := presented_relation datum 8
      (Word.product [Word.inverse cWord, Word.pow dWord 3,
        positiveWord (datum.F 2), Word.pow eWord 3, cWord])
      (Word.product [Word.pow dWord 3, positiveWord (datum.E 2),
        Word.pow eWord 3])
      (by simp [presentation, simulationRelator])
    simpa [dWord, eWord, cWord, mul_assoc] using h

theorem target_commutes (datum : Thue.StandingDatum) :
    Commute
      ((UniversalGroup.evalPositive (gen datum 2) (gen datum 3) datum.P)⁻¹ *
        gen datum 5 * UniversalGroup.evalPositive (gen datum 2) (gen datum 3) datum.P)
      (gen datum 6) := by
  have h := presented_relator_eq_one datum 13
  have hr : (presentation datum).relator 13 =
      Word.commutator kWord (pWord datum) := by simp [presentation]
  rw [hr] at h
  have h' : (gen datum 6)⁻¹ *
      (Word.eval (gen datum) (pWord datum))⁻¹ * gen datum 6 *
      Word.eval (gen datum) (pWord datum) = 1 := by
    simpa only [Word.eval_commutator, kWord, Word.eval_generator,
      ← mul_assoc] using h
  have hc := (commute_of_inverse_commutator_eq_one h').symm
  simpa [pWord, tWord, mul_assoc] using hc

def testCommutes (datum : Thue.StandingDatum)
    (Q : List (Fin 2)) : Prop :=
  Commute
    ((UniversalGroup.evalPositive (gen datum 2) (gen datum 3) Q)⁻¹ *
      gen datum 5 * UniversalGroup.evalPositive (gen datum 2) (gen datum 3) Q)
    (gen datum 6)

theorem rule_preserves_testCommutes (datum : Thue.StandingDatum)
    (l r : List (Fin 2)) (i : Fin 3) :
    testCommutes datum (l ++ datum.F i ++ r) ↔
      testCommutes datum (l ++ datum.E i ++ r) := by
  let d := gen datum 0
  let e := gen datum 1
  let s₁ := gen datum 2
  let s₂ := gen datum 3
  let c := gen datum 4
  let t := gen datum 5
  let k := gen datum 6
  let exponent := i.val + 1
  let L := UniversalGroup.evalPositive s₁ s₂ l
  let R := UniversalGroup.evalPositive s₁ s₂ r
  let F := UniversalGroup.evalPositive s₁ s₂ (datum.F i)
  let E := UniversalGroup.evalPositive s₁ s₂ (datum.E i)
  let qF := L * F * R
  let qE := L * E * R
  let I := exponent * 4 ^ l.length
  let J := exponent * 4 ^ r.length
  obtain ⟨hd₁, hd₂⟩ := d_letter_relations datum
  obtain ⟨he₁, he₂⟩ := e_letter_relations datum
  obtain ⟨hc₁, hc₂⟩ := c_letter_relations datum
  obtain ⟨htc, htd, hkc, hke⟩ := fixed_commutations datum
  have hd : ∀ s ∈ ({s₁, s₂} : Set (presentation datum).Group),
      d ^ 4 * s = s * d := by
    intro s hs
    rcases hs with (rfl | hs)
    · exact hd₁
    · simpa only [Set.mem_singleton_iff] using hs ▸ hd₂
  have he : ∀ s ∈ ({s₁, s₂} : Set (presentation datum).Group),
      e * s = s * e ^ 4 := by
    intro s hs
    rcases hs with (rfl | hs)
    · exact he₁
    · simpa only [Set.mem_singleton_iff] using hs ▸ he₂
  have hDL : d ^ I * L = L * d ^ exponent :=
    d_transport d s₁ s₂ hd l exponent
  have hER : e ^ exponent * R = R * e ^ J :=
    e_transport e s₁ s₂ he r exponent
  have hpackF : d ^ I * qF * e ^ J =
      L * (d ^ exponent * F * e ^ exponent) * R :=
    pack_context (d ^ I) (d ^ exponent) (e ^ exponent)
      L F R (e ^ J) hDL hER
  have hpackE : d ^ I * qE * e ^ J =
      L * (d ^ exponent * E * e ^ exponent) * R :=
    pack_context (d ^ I) (d ^ exponent) (e ^ exponent)
      L E R (e ^ J) hDL hER
  have hsim : c⁻¹ * (d ^ exponent * F * e ^ exponent) * c =
      d ^ exponent * E * e ^ exponent := by
    simpa [exponent, d, e, s₁, s₂, c, F, E, mul_assoc] using
      simulation_relation_semantic datum i
  have hAB : c⁻¹ * (d ^ I * qF * e ^ J) * c = d ^ I * qE * e ^ J := by
    rw [hpackF, hpackE]
    exact conjugate_context c L
      (d ^ exponent * F * e ^ exponent)
      (d ^ exponent * E * e ^ exponent) R
      (evalPositive_commute s₁ s₂ c hc₁ hc₂ l)
      (evalPositive_commute s₁ s₂ c hc₁ hc₂ r) hsim
  have hqF : UniversalGroup.evalPositive s₁ s₂ (l ++ datum.F i ++ r) = qF := by
    simp [qF, L, F, R, evalPositive_append, mul_assoc]
  have hqE : UniversalGroup.evalPositive s₁ s₂ (l ++ datum.E i ++ r) = qE := by
    simp [qE, L, E, R, evalPositive_append, mul_assoc]
  change Commute
      ((UniversalGroup.evalPositive s₁ s₂ (l ++ datum.F i ++ r))⁻¹ * t *
        UniversalGroup.evalPositive s₁ s₂ (l ++ datum.F i ++ r)) k ↔
    Commute
      ((UniversalGroup.evalPositive s₁ s₂ (l ++ datum.E i ++ r))⁻¹ * t *
        UniversalGroup.evalPositive s₁ s₂ (l ++ datum.E i ++ r)) k
  rw [hqF, hqE]
  rw [test_repack_commute_iff d e t k qF I J htd hke,
    test_repack_commute_iff d e t k qE I J htd hke]
  exact simulation_preserves_commute c t k
    (d ^ I * qF * e ^ J) (d ^ I * qE * e ^ J) hAB htc hkc

theorem thueStep_preserves_testCommutes (datum : Thue.StandingDatum)
    {u v : List (Fin 2)}
    (h : ThueStep (Thue.systemOf datum.F datum.E) u v) :
    testCommutes datum u ↔ testCommutes datum v := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, huv⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rule_preserves_testCommutes datum l r i
  · exact (rule_preserves_testCommutes datum l r i).symm

theorem thueEq_preserves_testCommutes (datum : Thue.StandingDatum)
    {u v : List (Fin 2)}
    (h : ThueEq (Thue.systemOf datum.F datum.E) u v) :
    testCommutes datum u ↔ testCommutes datum v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (thueStep_preserves_testCommutes datum hstep)

/-- The elementary direction of Borisov's simulation theorem.  It uses only
the defining relators: one Thue rewrite preserves commutation of `Q⁻¹tQ`
with `k`, and the target relator supplies the base case at `P`. -/
theorem criterion_forward
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P →
      (presentation datum).wordProblem (testWord Q) := by
  intro hQP
  have hcomm : testCommutes datum Q :=
    (thueEq_preserves_testCommutes datum hQP).mpr (target_commutes datum)
  let q := UniversalGroup.evalPositive (gen datum 2) (gen datum 3) Q
  let a := q⁻¹ * gen datum 5 * q
  have hcomm' : Commute a (gen datum 6) := by
    simpa [testCommutes, q, a] using hcomm
  have hone : a⁻¹ * (gen datum 6)⁻¹ * a * gen datum 6 = 1 :=
    (inverse_commutator_eq_one_iff a (gen datum 6)).mpr hcomm'
  rw [(presentation datum).wordProblem_iff_evalWord_eq_one]
  change Word.eval (gen datum) (testWord Q) = 1
  simpa [testWord, tWord, kWord, q, a, mul_assoc] using hone

end Borisov
end UniversalGroup
