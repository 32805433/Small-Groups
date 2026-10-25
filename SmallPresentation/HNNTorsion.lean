module

public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-! # Finite-order elements and torsion-freeness of HNN extensions -/
@[expose] public section

namespace SmallPresentationStatements.HNNTorsion

open HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} (φ : A ≃* B)

abbrev Syllable := ℤˣ × G

def block (a : Syllable (G := G)) : HNNExtension G A B φ :=
  t ^ (a.1 : ℤ) * of a.2

def eval (l : List (Syllable (G := G))) : HNNExtension G A B φ :=
  (l.map (block φ)).prod

@[simp] theorem eval_nil : eval φ [] = 1 := rfl
@[simp] theorem eval_cons (a : Syllable (G := G)) (l) :
    eval φ (a :: l) = block φ a * eval φ l := by simp [eval]
@[simp] theorem eval_append (l r : List (Syllable (G := G))) :
    eval φ (l ++ r) = eval φ l * eval φ r := by simp [eval]

theorem stable_conj (u : ℤˣ) (a : toSubgroup A B u) :
    (t : HNNExtension G A B φ) ^ (u : ℤ) * of (a : G) * t ^ (-(u : ℤ)) =
      of (toSubgroupEquiv φ u a : G) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [toSubgroupEquiv_one, Units.val_one, zpow_one, zpow_neg_one]
    exact (equiv_eq_conj (φ := φ) a).symm
  · simp only [toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one, neg_neg,
      zpow_one, zpow_neg_one]
    exact (equiv_symm_eq_conj (φ := φ) a).symm

theorem pinch (a b : Syllable (G := G)) (h : a.2 ∈ toSubgroup A B a.1)
    (hne : a.1 ≠ b.1) :
    block φ a * block φ b = of ((toSubgroupEquiv φ a.1 ⟨a.2, h⟩ : G) * b.2) := by
  have hb : b.1 = -a.1 := Int.units_ne_iff_eq_neg.mp hne.symm
  calc
    block φ a * block φ b =
        (t ^ (a.1 : ℤ) * of a.2 * t ^ (-(a.1 : ℤ))) * of b.2 := by
      simp [block, hb, mul_assoc]
    _ = _ := by rw [stable_conj φ a.1 ⟨a.2, h⟩, map_mul]

/-- Minimal stable-letter length among all conjugate words, allowing a base head. -/
def Minimal (l : List (Syllable (G := G))) : Prop :=
  ∀ (g : G) (r : List (Syllable (G := G))) (c : HNNExtension G A B φ),
    eval φ l = c * (of g * eval φ r) * c⁻¹ → l.length ≤ r.length

theorem Minimal.rotate_le {u v r : List (Syllable (G := G))} (hl : Minimal φ (u ++ v))
    (g : G) (h : eval φ (v ++ u) = of g * eval φ r) : (u ++ v).length ≤ r.length := by
  apply hl g r (eval φ u)
  rw [← h]
  simp [mul_assoc]

theorem exists_eval (x : HNNExtension G A B φ) :
    ∃ (g : G) (l : List (Syllable (G := G))), of g * eval φ l = x := by
  classical
  let d := Classical.choice (NormalWord.TransversalPair.nonempty G A B)
  let w := NormalWord.equiv φ d x
  exact ⟨w.head, w.toList, (NormalWord.equiv φ d).symm_apply_apply x⟩

theorem nil_or_last {α : Type*} (l : List α) : l = [] ∨ ∃ p a, l = p ++ [a] := by
  induction l using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton p a _ => exact Or.inr ⟨p, a, rfl⟩

theorem exists_minimal (x : HNNExtension G A B φ) :
    (∃ (g : G) (c : HNNExtension G A B φ), x = c * of g * c⁻¹) ∨
    ∃ (l : List (Syllable (G := G))) (c : HNNExtension G A B φ),
      l ≠ [] ∧ x = c * eval φ l * c⁻¹ ∧ Minimal φ l := by
  classical
  have hex : ∃ n, ∃ (g : G) (l : List (Syllable (G := G)))
      (c : HNNExtension G A B φ), l.length = n ∧ x = c * (of g * eval φ l) * c⁻¹ := by
    obtain ⟨g, l, rfl⟩ := exists_eval φ x
    exact ⟨l.length, g, l, 1, rfl, by simp⟩
  obtain ⟨g, l, c, hlen, hx⟩ := Nat.find_spec hex
  rcases nil_or_last l with rfl | ⟨p, a, rfl⟩
  · exact Or.inl ⟨g, c, by simpa using hx⟩
  · let r := p ++ [(a.1, a.2 * g)]
    have hr : eval φ r = eval φ (p ++ [a]) * of g := by
      simp [r, block, map_mul, mul_assoc]
    have hx' : x = (c * of g) * eval φ r * (c * of g)⁻¹ := by
      rw [hr, hx]
      group
    refine Or.inr ⟨r, c * of g, by simp [r], hx', ?_⟩
    intro g' r' d hd
    have hlen' : r.length = Nat.find hex := by simpa [r] using hlen
    rw [hlen']
    apply Nat.find_min' hex
    refine ⟨g', r', (c * of g) * d, rfl, ?_⟩
    rw [hx', hd]
    group

theorem Minimal.chain {l : List (Syllable (G := G))} (hl : Minimal φ l) :
    l.IsChain (fun a b ↦ a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b p q hsplit ha
  by_contra hne
  subst l
  have hshort := Minimal.rotate_le φ hl
    ((toSubgroupEquiv φ a.1 ⟨a.2, ha⟩ : G) * b.2) (r := q ++ p) (by
      simp only [List.cons_append, eval_cons, eval_append]
      rw [← mul_assoc (block φ a), pinch φ a b ha hne])
  simp only [List.length_append, List.length_cons] at hshort
  omega

theorem Minimal.ends {a b : Syllable (G := G)} {p : List (Syllable (G := G))}
    (hl : Minimal φ (b :: (p ++ [a]))) (ha : a.2 ∈ toSubgroup A B a.1) : a.1 = b.1 := by
  by_contra hne
  have hl' : Minimal φ ((b :: p) ++ [a]) := by simpa using hl
  have hshort := Minimal.rotate_le φ hl'
    ((toSubgroupEquiv φ a.1 ⟨a.2, ha⟩ : G) * b.2) (r := p) (by
      simp only [List.singleton_append, eval_cons]
      rw [← mul_assoc, pinch φ a b ha hne])
  simp only [List.length_append, List.length_cons, List.length_nil] at hshort
  omega

theorem Minimal.boundary {l : List (Syllable (G := G))} (hl : Minimal φ l) :
    ∀ a ∈ l.getLast?, ∀ b ∈ l.head?,
      a.2 ∈ toSubgroup A B a.1 → a.1 = b.1 := by
  intro a ha b hb
  have hhead := List.eq_cons_of_mem_head? hb
  rw [hhead] at ha hl
  by_cases htail : l.tail = []
  · have hab : b = a := by simpa [htail] using ha
    subst a
    exact fun _ ↦ rfl
  · have hlast : l.tail.getLast? = some a := by
      change ([b] ++ l.tail).getLast? = some a at ha
      rwa [List.getLast?_append_of_ne_nil _ htail] at ha
    obtain ⟨mid, hmid⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [hmid] at hl
    exact Minimal.ends φ hl

theorem repeat_chain {l : List (Syllable (G := G))} (hl : Minimal φ l)
    (hne : l ≠ []) (n : ℕ) :
    ((List.replicate n l).flatten).IsChain
      (fun a b ↦ a.2 ∈ toSubgroup A B a.1 → a.1 = b.1) := by
  apply (List.isChain_flatten (by simp [hne])).mpr
  constructor
  · intro r hr
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hr
    exact Minimal.chain φ hl
  · exact List.isChain_replicate_of_rel n (Minimal.boundary φ hl)

@[simp] theorem eval_repeat (l : List (Syllable (G := G))) (n : ℕ) :
    eval φ (List.replicate n l).flatten = eval φ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ']

theorem Minimal.pow_ne_one {l : List (Syllable (G := G))} (hl : Minimal φ l)
    (hne : l ≠ []) (n : ℕ) (hn : n ≠ 0) : eval φ l ^ n ≠ 1 := by
  intro hpow
  let wr : NormalWord.ReducedWord G A B := {
    head := 1
    toList := (List.replicate n l).flatten
    chain := repeat_chain φ hl hne n }
  have hprod : wr.prod φ = eval φ l ^ n := by
    change of (1 : G) * eval φ (List.replicate n l).flatten = _
    simp
  have he := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ wr (by
    rw [hprod, hpow]
    exact (of : G →* HNNExtension G A B φ).range.one_mem)
  have hin : l ∈ List.replicate n l := List.mem_replicate.mpr ⟨hn, rfl⟩
  have hempty : ∀ v ∈ List.replicate n l, v = [] := List.flatten_eq_nil_iff.mp he
  exact hne (hempty l hin)

/-- Every finite-order element in an HNN extension is conjugate into the base group. -/
theorem finiteOrder_conjugate_base (x : HNNExtension G A B φ) (hx : IsOfFinOrder x) :
    ∃ (g : G) (c : HNNExtension G A B φ), x = c * of g * c⁻¹ := by
  rcases exists_minimal φ x with hbase | ⟨l, c, hne, heq, hmin⟩
  · exact hbase
  · obtain ⟨n, hn, hpow⟩ := hx.exists_pow_eq_one
    have hc : (MulAut.conj c) (eval φ l ^ n) = (MulAut.conj c) 1 := by
      simpa only [map_pow, MulAut.conj_apply, map_one, ← heq] using hpow
    exact (Minimal.pow_ne_one φ hmin hne n hn.ne' ((MulAut.conj c).injective hc)).elim

/-- An HNN extension of a torsion-free group is torsion-free. -/
theorem torsionFree [IsMulTorsionFree G] : IsMulTorsionFree (HNNExtension G A B φ) := by
  apply IsMulTorsionFree.of_not_isOfFinOrder
  intro x hx hfinite
  obtain ⟨g, c, rfl⟩ := finiteOrder_conjugate_base φ x hfinite
  obtain ⟨n, hn, hpow⟩ := hfinite.exists_pow_eq_one
  have hc : (MulAut.conj c) ((of g : HNNExtension G A B φ) ^ n) =
      (MulAut.conj c) 1 := by
    simpa only [map_pow, MulAut.conj_apply, map_one] using hpow
  have hi : (of g : HNNExtension G A B φ) ^ n = 1 := (MulAut.conj c).injective hc
  have hg : g ^ n = 1 := HNNExtension.of_injective φ (by simpa using hi)
  have hg1 : g = 1 := (pow_eq_one_iff_left hn.ne').mp hg
  apply hx
  simp [hg1]

end SmallPresentationStatements.HNNTorsion
