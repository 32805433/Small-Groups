module

public import SmallPresentation.Basic

/-! # Literal signed words and their evaluation -/
@[expose] public section

namespace SmallPresentationStatements.Word

variable {n m : ℕ} {G H : Type*} [Group G] [Group H]

def gen (i : Fin n) : Word n := [(i, true)]

def inverse (w : Word n) : Word n :=
  (w.reverse).map fun a ↦ (a.1, !a.2)

def power (w : Word n) (k : ℕ) : Word n := (List.replicate k w).flatten

def conjugate (w v : Word n) : Word n := inverse v ++ w ++ v

def commutator (w v : Word n) : Word n := inverse w ++ inverse v ++ w ++ v

def subst (f : Fin n → Word m) (w : Word n) : Word m :=
  w.flatMap fun a ↦ if a.2 then f a.1 else inverse (f a.1)

def eval (f : Fin n → G) (w : Word n) : G := FreeGroup.lift f (FreeGroup.mk w)

@[simp] theorem eval_nil (f : Fin n → G) : eval f [] = 1 := by
  simp [eval, ← FreeGroup.one_eq_mk]

@[simp] theorem eval_gen (f : Fin n → G) (i : Fin n) : eval f (gen i) = f i := by
  simp [eval, gen, FreeGroup.lift_mk]

@[simp] theorem eval_append (f : Fin n → G) (u v : Word n) :
    eval f (u ++ v) = eval f u * eval f v := by
  simp [eval, ← FreeGroup.mul_mk]

@[simp] theorem eval_cons (f : Fin n → G) (a : SignedGenerator n) (w : Word n) :
    eval f (a :: w) = (if a.2 then f a.1 else (f a.1)⁻¹) * eval f w := by
  cases a with
  | mk i s => cases s <;> simp [eval, FreeGroup.lift_mk]

@[simp] theorem eval_inverse (f : Fin n → G) (w : Word n) :
    eval f (inverse w) = (eval f w)⁻¹ := by
  induction w with
  | nil => simp [inverse]
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp_all [inverse, List.reverse_cons, List.map_append]

@[simp] theorem eval_power (f : Fin n → G) (w : Word n) (k : ℕ) :
    eval f (power w k) = eval f w ^ k := by
  simp [eval, power, ← FreeGroup.pow_mk]

@[simp] theorem eval_conjugate (f : Fin n → G) (w v : Word n) :
    eval f (conjugate w v) = (eval f v)⁻¹ * eval f w * eval f v := by
  simp [conjugate, mul_assoc]

@[simp] theorem eval_commutator (f : Fin n → G) (w v : Word n) :
    eval f (commutator w v) = (eval f w)⁻¹ * (eval f v)⁻¹ * eval f w * eval f v := by
  simp [commutator, mul_assoc]

@[simp] theorem eval_subst (f : Fin n → Word m) (g : Fin m → G) (w : Word n) :
    eval g (subst f w) = eval (fun i ↦ eval g (f i)) w := by
  induction w with
  | nil => simp [subst]
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp_all [subst]

theorem map_eval (h : G →* H) (f : Fin n → G) (w : Word n) :
    h (eval f w) = eval (fun i ↦ h (f i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp_all

theorem inverse_primrec : Primrec (@inverse n) := by
  apply Primrec.list_map Primrec.list_reverse
  exact (Primrec.fst.comp Primrec.snd).pair
    (Primrec.not.comp (Primrec.snd.comp Primrec.snd))

theorem subst_primrec (f : Fin n → Word m) : Primrec (subst f) := by
  apply Primrec.list_flatMap Primrec.id
  have hf : Primrec fun p : Word n × SignedGenerator n ↦ f p.2.1 :=
    Primrec.fin_app.comp (Primrec.const f) (Primrec.fst.comp Primrec.snd)
  apply (Primrec.cond (Primrec.snd.comp Primrec.snd) hf (inverse_primrec.comp hf)).of_eq
  rintro ⟨w, i, b⟩
  cases b <;> rfl

theorem subst_computable (f : Fin n → Word m) : Computable (subst f) :=
  (subst_primrec f).to_comp

/-- Weighted exponent sum; this is syntax, so it is computable without solving a word problem. -/
def exponent (weight : Fin n → ℤ) (w : Word n) : ℤ :=
  (w.map fun a ↦ if a.2 then weight a.1 else -weight a.1).sum

@[simp] theorem exponent_nil (weight : Fin n → ℤ) : exponent weight [] = 0 := by
  simp [exponent]

@[simp] theorem exponent_cons (weight : Fin n → ℤ) (a : SignedGenerator n) (w : Word n) :
    exponent weight (a :: w) =
      (if a.2 then weight a.1 else -weight a.1) + exponent weight w := by
  simp [exponent]

theorem eval_zpowers (z : G) (weight : Fin n → ℤ) (w : Word n) :
    eval (fun i ↦ z ^ weight i) w = z ^ exponent weight w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp_all [zpow_add]

@[simp] theorem eval_all_one (w : Word n) : eval (fun _ ↦ (1 : G)) w = 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp_all

@[simp] theorem eval_flatten (f : Fin n → G) (ws : List (Word n)) :
    eval f ws.flatten = (ws.map (eval f)).prod := by
  induction ws with
  | nil => simp
  | cons w ws ih => simp [ih]

end SmallPresentationStatements.Word
