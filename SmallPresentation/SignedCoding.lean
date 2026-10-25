module

public import SmallPresentation.PackingWords
public import SmallPresentation.Computability

/-!
# The literal signed-code quotient and permutation symmetry

This constructs `B_d` from the manuscript and proves that every ordered pair
defines a homomorphism from the input. Permutations act on this exact quotient.
Injectivity and the relative classifying-space theorem still require the
small-cancellation argument; neither is asserted here.
-/
@[expose] public section

namespace SmallPresentationStatements.SignedCoding

open Word

variable {L d : ℕ}

def codeWord (r u : Fin d) (j : Fin 2) : Word d :=
  subst ![gen r, gen u] (![code₁, code₂] j)

def row (Q : FP 2 L) (r u : Fin d) (i : Fin L) : Word d :=
  subst (codeWord r u) (Q.relator i)

def relators (Q : FP 2 L) (d : ℕ) : Set (FreeGroup (Fin d)) :=
  {w | ∃ r u : Fin d, r ≠ u ∧ ∃ i : Fin L, w = FreeGroup.mk (row Q r u i)}

abbrev CodedGroup (Q : FP 2 L) (d : ℕ) := PresentedGroup (relators Q d)

theorem eval_presented {n : ℕ} (S : Set (FreeGroup (Fin n))) (w : Word n) :
    eval (PresentedGroup.of (rels := S)) w = PresentedGroup.mk S (FreeGroup.mk w) := by
  have h : FreeGroup.lift (PresentedGroup.of (rels := S)) = PresentedGroup.mk S := by
    ext i
    rfl
  exact DFunLike.congr_fun h _

theorem row_eq_one (Q : FP 2 L) (r u : Fin d) (hru : r ≠ u) (i : Fin L) :
    eval (PresentedGroup.of (rels := relators Q d)) (row Q r u i) = 1 := by
  rw [eval_presented]
  exact PresentedGroup.one_of_mem ⟨r, u, hru, i, rfl⟩

def sourceHom (Q : FP 2 L) (r u : Fin d) (hru : r ≠ u) :
    Q.Group →* CodedGroup Q d :=
  PresentedGroup.toGroup
    (f := fun j ↦ eval (PresentedGroup.of (rels := relators Q d)) (codeWord r u j)) (by
      rintro _ ⟨i, rfl⟩
      change eval (fun j ↦ eval (PresentedGroup.of (rels := relators Q d))
        (codeWord r u j)) (Q.relator i) = 1
      rw [← eval_subst]
      exact row_eq_one Q r u hru i)

theorem eval_codeWord {H : Type*} [Group H] (f : Fin d → H) (r u : Fin d) (j : Fin 2) :
    eval f (codeWord r u j) = eval ![f r, f u] (![code₁, code₂] j) := by
  simp only [codeWord, eval_subst]
  congr 1
  funext k
  fin_cases k <;> simp

theorem permuted_row (Q : FP 2 L) (σ : Equiv.Perm (Fin d))
    (r u : Fin d) (hru : r ≠ u) (i : Fin L) :
    eval (fun j ↦ PresentedGroup.of (rels := relators Q d) (σ j)) (row Q r u i) = 1 := by
  have heq : eval (fun j ↦ PresentedGroup.of (rels := relators Q d) (σ j))
      (row Q r u i) =
      eval (PresentedGroup.of (rels := relators Q d)) (row Q (σ r) (σ u) i) := by
    simp only [row, eval_subst]
    congr 1
    funext j
    rw [eval_codeWord, eval_codeWord]
  rw [heq]
  exact row_eq_one Q (σ r) (σ u) (fun h ↦ hru (σ.injective h)) i

def permutationHom (Q : FP 2 L) (σ : Equiv.Perm (Fin d)) :
    CodedGroup Q d →* CodedGroup Q d :=
  PresentedGroup.toGroup
    (f := fun j ↦ PresentedGroup.of (rels := relators Q d) (σ j)) (by
      rintro _ ⟨r, u, hru, i, rfl⟩
      exact permuted_row Q σ r u hru i)

@[simp] theorem permutationHom_of (Q : FP 2 L) (σ : Equiv.Perm (Fin d)) (j : Fin d) :
    permutationHom Q σ (PresentedGroup.of j) = PresentedGroup.of (σ j) :=
  PresentedGroup.toGroup.of _

theorem permutationHom_comp (Q : FP 2 L) (σ τ : Equiv.Perm (Fin d)) :
    (permutationHom Q σ).comp (permutationHom Q τ) = permutationHom Q (τ.trans σ) := by
  ext j
  simp

def permutationEquiv (Q : FP 2 L) (σ : Equiv.Perm (Fin d)) :
    CodedGroup Q d ≃* CodedGroup Q d where
  toFun := permutationHom Q σ
  invFun := permutationHom Q σ.symm
  left_inv := by
    have h : (permutationHom Q σ.symm).comp (permutationHom Q σ) = MonoidHom.id _ := by
      ext j
      simp
    exact DFunLike.congr_fun h
  right_inv := by
    have h : (permutationHom Q σ).comp (permutationHom Q σ.symm) = MonoidHom.id _ := by
      ext j
      simp
    exact DFunLike.congr_fun h
  map_mul' := map_mul _

/-- Permutations preserve the ordered pair and code type exactly. -/
theorem permutation_source (Q : FP 2 L) (σ : Equiv.Perm (Fin d))
    (r u : Fin d) (hru : r ≠ u) :
    (permutationHom Q σ).comp (sourceHom Q r u hru) =
      sourceHom Q (σ r) (σ u) (fun h ↦ hru (σ.injective h)) := by
  ext j
  simp only [MonoidHom.comp_apply, sourceHom, PresentedGroup.toGroup.of, map_eval]
  simp only [permutationHom_of, eval_codeWord]

end SmallPresentationStatements.SignedCoding
