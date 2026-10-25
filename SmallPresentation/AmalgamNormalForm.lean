module

public import Mathlib.GroupTheory.PushoutI
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

/-! # Cyclic reduction in an injective amalgam -/
@[expose] public section

namespace SmallPresentationStatements.AmalgamNormalForm

open Monoid

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {H : Type*} [Group H]
variable (φ : ∀ i, H →* G i)

abbrev Letter := Σ i, G i

def eval (l : List (Letter (G := G))) : PushoutI φ :=
  (l.map fun a ↦ PushoutI.of a.1 a.2).prod

@[simp] theorem eval_nil : eval φ [] = 1 := rfl
@[simp] theorem eval_cons (a : Letter (G := G)) (l) :
    eval φ (a :: l) = PushoutI.of a.1 a.2 * eval φ l := by simp [eval]
@[simp] theorem eval_append (l r : List (Letter (G := G))) :
    eval φ (l ++ r) = eval φ l * eval φ r := by simp [eval]

/-- Minimal length among all lists representing a conjugate. -/
def Minimal (l : List (Letter (G := G))) : Prop :=
  ∀ (l' : List (Letter (G := G))) (c : PushoutI φ),
    eval φ l = c * eval φ l' * c⁻¹ → l.length ≤ l'.length

theorem Minimal.of_eval_eq {l l' : List (Letter (G := G))} (hl : Minimal φ l)
    (h : eval φ l = eval φ l') : l.length ≤ l'.length :=
  hl l' 1 (by simpa using h)

theorem Minimal.rotate_le {u v r : List (Letter (G := G))} (hl : Minimal φ (u ++ v))
    (h : eval φ (v ++ u) = eval φ r) : (u ++ v).length ≤ r.length := by
  apply hl r (eval φ u)
  rw [← h]
  simp [mul_assoc]

theorem exists_eval [Nonempty ι] (x : PushoutI φ) :
    ∃ l : List (Letter (G := G)), eval φ l = x := by
  induction x using PushoutI.induction_on with
  | of i g => exact ⟨[⟨i, g⟩], by simp⟩
  | base h =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨[⟨i, φ i h⟩], by simp [PushoutI.of_apply_eq_base]⟩
  | mul x y hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨r, rfl⟩ := hy
    exact ⟨l ++ r, by simp⟩

theorem exists_minimal [Nonempty ι] (x : PushoutI φ) :
    ∃ (l : List (Letter (G := G))) (c : PushoutI φ),
      x = c * eval φ l * c⁻¹ ∧ Minimal φ l := by
  classical
  have hex : ∃ n, ∃ (l : List (Letter (G := G))) (c : PushoutI φ),
      l.length = n ∧ x = c * eval φ l * c⁻¹ := by
    obtain ⟨l, rfl⟩ := exists_eval φ x
    exact ⟨l.length, l, 1, rfl, by simp⟩
  obtain ⟨l, c, hlen, hx⟩ := Nat.find_spec hex
  refine ⟨l, c, hx, fun r d hd ↦ ?_⟩
  rw [hlen]
  apply Nat.find_min' hex
  refine ⟨r, c * d, rfl, ?_⟩
  rw [hx, hd]
  group

theorem Minimal.chain {l : List (Letter (G := G))} (hl : Minimal φ l) :
    l.IsChain (fun a b ↦ a.1 ≠ b.1) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b u v hsplit heq
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp at heq
  subst j
  subst l
  have hshort := Minimal.of_eval_eq φ hl (l' := u ++ ⟨i, a * b⟩ :: v) (by
    simp only [eval_append, eval_cons, map_mul, mul_assoc])
  simp only [List.length_append, List.length_cons] at hshort
  omega

theorem Minimal.not_mem_range {l : List (Letter (G := G))} (hl : Minimal φ l)
    (hlen : 2 ≤ l.length) : ∀ a ∈ l, a.2 ∉ (φ a.1).range := by
  intro a ha hbase
  obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp ha
  obtain ⟨h, hh⟩ := hbase
  have hne : v ++ u ≠ [] := by
    intro he
    have hlen' := congrArg List.length he
    simp only [List.length_append, List.length_nil] at hlen'
    simp only [List.length_append, List.length_cons] at hlen
    omega
  obtain ⟨b, tail, htail⟩ := List.exists_cons_of_ne_nil hne
  let r : List (Letter (G := G)) := ⟨b.1, φ b.1 h * b.2⟩ :: tail
  have hshort := Minimal.rotate_le φ hl (r := r) (by
    change eval φ ((a :: v) ++ u) = eval φ r
    rw [List.cons_append, htail]
    simp only [eval_cons, r, map_mul]
    rw [← hh, PushoutI.of_apply_eq_base, PushoutI.of_apply_eq_base]
    simp [mul_assoc])
  have hlen' := congrArg List.length htail
  simp only [List.length_append, List.length_cons] at hshort hlen'
  dsimp [r] at hshort
  omega

theorem Minimal.ends_ne {a b : Letter (G := G)} {l : List (Letter (G := G))}
    (hl : Minimal φ (a :: (l ++ [b]))) : a.1 ≠ b.1 := by
  intro heq
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp at heq
  subst j
  have hshort := Minimal.rotate_le φ (show Minimal φ ([⟨i, a⟩] ++ (l ++ [⟨i, b⟩])) from hl)
    (r := l ++ [⟨i, b * a⟩]) (by simp only [eval_append, eval_cons, eval_nil, map_mul, mul_assoc, mul_one])
  simp only [List.length_append, List.length_cons, List.length_nil] at hshort
  omega

theorem Minimal.boundary {l : List (Letter (G := G))} (hl : Minimal φ l)
    (hlen : 2 ≤ l.length) :
    ∀ a ∈ l.getLast?, ∀ b ∈ l.head?, a.1 ≠ b.1 := by
  intro a ha b hb
  have hhead := List.eq_cons_of_mem_head? hb
  rw [hhead] at ha hl hlen
  have htail : l.tail ≠ [] := by
    intro he
    simp [he] at hlen
  have hlast : l.tail.getLast? = some a := by
    change ([b] ++ l.tail).getLast? = some a at ha
    rwa [List.getLast?_append_of_ne_nil _ htail] at ha
  obtain ⟨mid, hmid⟩ := List.getLast?_eq_some_iff.mp hlast
  rw [hmid] at hl
  exact (Minimal.ends_ne φ hl).symm

theorem repeat_chain {l : List (Letter (G := G))} (hl : Minimal φ l)
    (hlen : 2 ≤ l.length) (n : ℕ) :
    ((List.replicate n l).flatten).IsChain (fun a b ↦ a.1 ≠ b.1) := by
  have hne : l ≠ [] := by intro h; simp [h] at hlen
  apply (List.isChain_flatten (by simp [hne])).mpr
  constructor
  · intro r hr
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hr
    exact Minimal.chain φ hl
  · exact List.isChain_replicate_of_rel n (Minimal.boundary φ hl hlen)

@[simp] theorem eval_repeat (l : List (Letter (G := G))) (n : ℕ) :
    eval φ (List.replicate n l).flatten = eval φ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ']

theorem word_eval (w : CoprodI.Word G) :
    PushoutI.ofCoprodI w.prod = eval φ w.toList := by
  simp [CoprodI.Word.prod, eval, map_list_prod, List.map_map, Function.comp_def]

theorem Minimal.pow_ne_one (hφ : ∀ i, Function.Injective (φ i))
    {l : List (Letter (G := G))} (hl : Minimal φ l) (hlen : 2 ≤ l.length)
    (n : ℕ) (hn : n ≠ 0) : eval φ l ^ n ≠ 1 := by
  intro hpow
  let r := (List.replicate n l).flatten
  have hmem : ∀ a ∈ r, a ∈ l := by
    intro a ha
    change a ∈ (List.replicate n l).flatten at ha
    obtain ⟨v, hv, hav⟩ := List.mem_flatten.mp ha
    have hv' : v = l := (List.mem_replicate.mp hv).2
    exact hv' ▸ hav
  have hbase : ∀ a ∈ r, a.2 ∉ (φ a.1).range :=
    fun a ha ↦ Minimal.not_mem_range φ hl hlen a (hmem a ha)
  let wr : CoprodI.Word G := {
    toList := r
    ne_one := fun a ha h ↦ hbase a ha (h ▸ (φ a.1).range.one_mem)
    chain_ne := repeat_chain φ hl hlen n }
  have hred : PushoutI.Reduced φ wr := hbase
  have he : wr = CoprodI.Word.empty :=
    hred.eq_empty_of_mem_range hφ (by
      rw [word_eval]
      change eval φ r ∈ (PushoutI.base φ).range
      simp only [r, eval_repeat, hpow]
      exact (PushoutI.base φ).range.one_mem)
  have hrnil : r = [] := congrArg CoprodI.Word.toList he
  have hln : l ≠ [] := by intro h; simp [h] at hlen
  have hin : l ∈ List.replicate n l := List.mem_replicate.mpr ⟨hn, rfl⟩
  have hempty : ∀ v ∈ List.replicate n l, v = [] := List.flatten_eq_nil_iff.mp hrnil
  exact hln (hempty l hin)

/-- A finite-order element of an injective amalgam is conjugate into a factor. -/
theorem finiteOrder_conjugate_factor [Nonempty ι]
    (hφ : ∀ i, Function.Injective (φ i))
    (x : PushoutI φ) (hx : IsOfFinOrder x) :
    ∃ (i : ι) (g : G i) (c : PushoutI φ), x = c * PushoutI.of i g * c⁻¹ := by
  obtain ⟨l, c, heq, hmin⟩ := exists_minimal φ x
  have hlen : l.length < 2 := by
    by_contra h
    have hlarge : 2 ≤ l.length := Nat.le_of_not_gt h
    obtain ⟨n, hn, hpow⟩ := hx.exists_pow_eq_one
    have hc : (MulAut.conj c) (eval φ l ^ n) = (MulAut.conj c) 1 := by
      simpa only [map_pow, MulAut.conj_apply, map_one, ← heq] using hpow
    exact Minimal.pow_ne_one φ hφ hmin hlarge n hn.ne' ((MulAut.conj c).injective hc)
  cases l with
  | nil =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, 1, c, by simpa using heq⟩
  | cons a tail =>
    have ht : tail = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_cons] at hlen
      omega
    subst tail
    exact ⟨a.1, a.2, c, by simpa using heq⟩

end SmallPresentationStatements.AmalgamNormalForm
