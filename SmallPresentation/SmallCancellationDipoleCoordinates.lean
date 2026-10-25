module

public import SmallPresentation.SmallCancellationGeometryIdentityBands

/-! Exact incidence coordinates for removing two indexed rows. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowDeletion

variable {O : Type} (F : O → Type) (i j : O) (hij : i ≠ j)

/-- The occurrence indices retained after removing exactly two distinct rows. -/
abbrev Remaining := {o : O // o ≠ i ∧ o ≠ j}

/-- Retained incidences and the two removed fibers partition the original incidences. -/
def embed : (Σ o : Remaining i j, F o.val) ⊕ (F i ⊕ F j) → Σ o, F o
  | .inl ⟨o, d⟩ => ⟨o.val, d⟩
  | .inr (.inl d) => ⟨i, d⟩
  | .inr (.inr d) => ⟨j, d⟩

include hij in
theorem embed_injective : Function.Injective (embed F i j) := by
  intro x y h
  rcases x with ⟨⟨o, ho⟩, d⟩ | (d | d) <;>
    rcases y with ⟨⟨p, hp⟩, e⟩ | (e | e)
  · have hop : o = p := congrArg Sigma.fst h
    subst p
    have hde : d = e := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst e
    rfl
  · exact False.elim (ho.1 (congrArg Sigma.fst h))
  · exact False.elim (ho.2 (congrArg Sigma.fst h))
  · exact False.elim (hp.1 (congrArg Sigma.fst h).symm)
  · have hde : d = e := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst e
    rfl
  · exact False.elim (hij (congrArg Sigma.fst h))
  · exact False.elim (hp.2 (congrArg Sigma.fst h).symm)
  · exact False.elim (hij (congrArg Sigma.fst h).symm)
  · have hde : d = e := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst e
    rfl

theorem embed_surjective : Function.Surjective (embed F i j) := by
  rintro ⟨o, d⟩
  by_cases hi : o = i
  · subst o; exact ⟨.inr (.inl d), rfl⟩
  by_cases hj : o = j
  · subst o; exact ⟨.inr (.inr d), rfl⟩
  exact ⟨.inl ⟨⟨o, hi, hj⟩, d⟩, rfl⟩

/-- A concrete partition equivalence preserves every retained occurrence and its corner. -/
noncomputable def coordinates : (Σ o : Remaining i j, F o.val) ⊕ (F i ⊕ F j) ≃ Σ o, F o :=
  Equiv.ofBijective (embed F i j) ⟨embed_injective F i j hij, embed_surjective F i j⟩

@[simp] theorem coordinates_apply (d) : coordinates F i j hij d = embed F i j d := rfl

variable {A B R : Type}

/-- Pair opposite row fibers through a specified correspondence. -/
def interchange (e : A ≃ B) : Equiv.Perm (A ⊕ B) where
  toFun
    | .inl a => .inr (e a)
    | .inr b => .inl (e.symm b)
  invFun
    | .inl a => .inr (e a)
    | .inr b => .inl (e.symm b)
  left_inv d := by cases d <;> simp
  right_inv d := by cases d <;> simp

theorem interchange_involutive (e : A ≃ B) : Function.Involutive (interchange e) := by
  intro d
  cases d <;> simp [interchange]

theorem interchange_ne (e : A ≃ B) (d : A ⊕ B) : interchange e d ≠ d := by
  cases d <;> simp [interchange]

/-- Retained incidences are fixed while all removed incidences are paired. -/
def corridor (e : A ≃ B) : Equiv.Perm (R ⊕ (A ⊕ B)) :=
  Equiv.sumCongr (Equiv.refl R) (interchange e)

theorem corridor_involutive (e : A ≃ B) : Function.Involutive (corridor (R := R) e) := by
  intro d
  rcases d with d | d
  · rfl
  · exact congrArg Sum.inr (interchange_involutive e d)

theorem corridor_fixed_iff (e : A ≃ B) (d : R ⊕ (A ⊕ B)) :
    corridor e d = d ↔ ∃ r, d = Sum.inl r := by
  rcases d with d | d
  · exact ⟨fun _ ↦ ⟨d, rfl⟩, fun _ ↦ rfl⟩
  · simp [corridor, interchange_ne]

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RowDeletion
