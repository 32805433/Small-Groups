module

public import SmallPresentation.Words

/-! # Computable word reductions and natural-number indexed families -/
@[expose] public section

namespace SmallPresentationStatements

open Encodable

def wordOfNat (n : ℕ) (j : ℕ) : Word n := (decode j).getD []

theorem wordOfNat_computable (n : ℕ) : Computable (wordOfNat n) :=
  Computable.decode.option_getD (Computable.const [])

@[simp] theorem wordOfNat_encode {n : ℕ} (w : Word n) : wordOfNat n (encode w) = w := by
  simp [wordOfNat]

theorem computablePred_precomp {α β : Type*} [Primcodable α] [Primcodable β]
    {p : β → Prop} (hp : ComputablePred p) {f : α → β} (hf : Computable f) :
    ComputablePred (fun x ↦ p (f x)) := by
  obtain ⟨d, hd⟩ := hp
  exact ⟨fun x ↦ d (f x), hd.comp hf⟩

namespace FP

variable {n m n' m' : ℕ}

@[simp] theorem eval_of (P : FP n m) (w : Word n) :
    Word.eval (PresentedGroup.of (rels := P.relSet)) w =
      PresentedGroup.mk P.relSet (FreeGroup.mk w) := by
  have h : FreeGroup.lift (PresentedGroup.of (rels := P.relSet)) =
      PresentedGroup.mk P.relSet := by
    ext i
    rfl
  exact DFunLike.congr_fun h _

theorem exists_word (P : FP n m) (x : P.Group) :
    ∃ w : Word n, Word.eval (PresentedGroup.of (rels := P.relSet)) w = x := by
  obtain ⟨g, rfl⟩ := PresentedGroup.mk_surjective P.relSet x
  obtain ⟨w, rfl⟩ := Quot.exists_rep g
  exact ⟨w, eval_of P w⟩

theorem eval_relator (P : FP n m) (i : Fin m) :
    Word.eval (PresentedGroup.of (rels := P.relSet)) (P.relator i) = 1 := by
  rw [eval_of]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

/-- A fixed embedding gives a computable word substitution, without a uniform procedure
for choosing embeddings. -/
theorem wordProblem_reduction_of_injective {P : FP n m} {Q : FP n' m'}
    (f : P.Group →* Q.Group) (hf : Function.Injective f) :
    ∃ σ : Word n → Word n', Computable σ ∧
      ∀ w, Q.wordProblem (σ w) ↔ P.wordProblem w := by
  choose u hu using fun i : Fin n ↦ Q.exists_word (f (PresentedGroup.of i))
  refine ⟨Word.subst u, Word.subst_computable u, ?_⟩
  intro w
  have h : Word.eval (PresentedGroup.of (rels := Q.relSet)) (Word.subst u w) =
      f (Word.eval (PresentedGroup.of (rels := P.relSet)) w) := by
    rw [Word.eval_subst, Word.map_eval]
    congr 1
    funext i
    exact hu i
  change PresentedGroup.mk Q.relSet (FreeGroup.mk (Word.subst u w)) = 1 ↔
    PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1
  rw [← eval_of, h, ← eval_of]
  exact ⟨fun h ↦ hf (h.trans f.map_one.symm), fun h ↦ h ▸ f.map_one⟩

theorem wordProblem_undecidable_of_injective {P : FP n m} {Q : FP n' m'}
    (f : P.Group →* Q.Group) (hf : Function.Injective f)
    (hP : ¬ ComputablePred P.wordProblem) : ¬ ComputablePred Q.wordProblem := by
  obtain ⟨σ, hσ, h⟩ := wordProblem_reduction_of_injective f hf
  intro hQ
  exact hP ((computablePred_precomp hQ hσ).of_eq h)

/-- The exact enumeration bridge: the encoding is a computable right inverse. -/
theorem isAdianRabinFamily_of_wordProblem_reduction (P : FP n m)
    (R : Word n → FP n' m')
    (hR : Computable₂ fun w i ↦ (R w).relator i)
    (hiff : ∀ w, (R w).presentsTrivial ↔ P.wordProblem w)
    (hP : ¬ ComputablePred P.wordProblem) :
    IsAdianRabinFamily (fun j ↦ R (wordOfNat n j)) := by
  constructor
  · exact hR.comp ((wordOfNat_computable n).comp Computable.fst) Computable.snd
  · intro h
    apply hP
    apply (computablePred_precomp h Computable.encode).of_eq
    intro w
    simpa using hiff w

end FP

theorem IsUniversal.of_injective {G H : Type*} [Group G] [Group H]
    (hG : IsUniversal G) (f : G →* H) (hf : Function.Injective f) : IsUniversal H := by
  intro n m Q
  obtain ⟨g, hg⟩ := hG n m Q
  exact ⟨f.comp g, hf.comp hg⟩

theorem IsUniversal.wordProblem_undecidable {n m : ℕ} {P : FP n m}
    (hP : IsUniversal P.Group)
    (hseed : ∃ n' m', ∃ Q : FP n' m', ¬ ComputablePred Q.wordProblem) :
    ¬ ComputablePred P.wordProblem := by
  obtain ⟨n', m', Q, hQ⟩ := hseed
  obtain ⟨f, hf⟩ := hP n' m' Q
  exact FP.wordProblem_undecidable_of_injective f hf hQ

end SmallPresentationStatements
