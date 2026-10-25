module

public import SmallPresentation.GordonWords

/-! # The collapse half of the Gordon attachment -/
@[expose] public section

namespace SmallPresentationStatements.Gordon

open Word

variable {m : ℕ} (P : FP 2 m) (w : Word 2)

theorem source_row (i : Fin m) :
    (presentation P w).relator i.castSucc = subst sourceImages (P.relator i) := by
  simp [presentation, sourceRows, Nat.ne_of_lt i.isLt]

theorem detector_row : (presentation P w).relator (Fin.last m) = detector w := by
  simp [presentation]

def sourceHom : P.Group →* (presentation P w).Group :=
  PresentedGroup.toGroup (f := fun i ↦
    eval (PresentedGroup.of (rels := (presentation P w).relSet)) (sourceImages i)) (by
      rintro _ ⟨i, rfl⟩
      change eval _ (P.relator i) = 1
      rw [← eval_subst, ← source_row P w i]
      exact FP.eval_relator _ _)

theorem source_word_eq_one (hw : P.wordProblem w) :
    eval (PresentedGroup.of (rels := (presentation P w).relSet)) (subst sourceImages w) = 1 := by
  have h := congrArg (sourceHom P w) hw
  rw [map_one] at h
  rw [← FP.eval_of P w] at h
  rw [map_eval] at h
  simpa [eval_subst, sourceHom] using h

/-- The remaining source relator must kill the cyclic specialization `b=z`, `s=z³`. -/
def CyclicCollapse : Prop :=
  ∀ (G : Type) [Group G] (z : G),
    (∀ i, eval ![z, z ^ 3] (P.relator i) = 1) → z = 1

theorem collapse (hP : CyclicCollapse P) (hw : P.wordProblem w) :
    (presentation P w).presentsTrivial := by
  let f : Fin 2 → (presentation P w).Group := PresentedGroup.of
  have hword : eval f (subst sourceImages w) = 1 := source_word_eq_one P w hw
  have hdet : eval f (detector w) = 1 := by
    rw [← detector_row P w]
    exact FP.eval_relator _ _
  have hb : f 1 = 1 := by
    have h := congrArg (fun x ↦ eval f beta ^ 3 * x * (eval f beta ^ 3)⁻¹) hdet
    have hinv : (f 1)⁻¹ = 1 := by
      simpa [detector, hword, mul_assoc] using h
    exact inv_eq_one.mp hinv
  have halpha : eval f alpha = 1 := by simp [alpha, hb]
  have hbeta : eval f beta = f 0 := by simp [beta, halpha, hb]
  have hsource : (fun i ↦ eval f (sourceImages i)) = ![f 0, f 0 ^ 3] := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [sourceImages, sourceB, hb, halpha, hbeta]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [sourceImages, sourceS, hb, halpha, hbeta]
  have ha : f 0 = 1 := hP _ (f 0) (by
    intro i
    rw [← hsource, ← eval_subst, ← source_row P w i]
    exact FP.eval_relator _ _)
  have hgen (i : Fin 2) : f i = 1 := by
    refine Fin.cases ha (fun j ↦ ?_) i
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hb
  have hall (g : (presentation P w).Group) : g = 1 := by
    have hmem : g ∈ (⊥ : Subgroup (presentation P w).Group) :=
      PresentedGroup.generated_by _ ⊥ (fun i ↦ by exact hgen i) g
    exact hmem
  exact ⟨fun x y ↦ (hall x).trans (hall y).symm⟩

end SmallPresentationStatements.Gordon
