module

public import SmallPresentation.GordonInjection
public import SmallPresentation.ExternalAmalgam
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# The exact Gordon presentation embeds into its amalgam

The reverse homomorphism below checks all five attachment equations after the four
literal eliminations. Its composition with the existing witness map is the identity.
Torsion-freeness then follows from the generic amalgam torsion theorem, with the two
edge injections supplied by the checked Gordon free-basis proofs.
-/
@[expose] public section

namespace SmallPresentationStatements.Gordon.UpstreamBridge

open UniversalGroup.Gordon.Amalgam

variable {m : ℕ} (P : FP 2 m)
variable (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
variable (w : Word 2)

abbrev targetGenerator : Fin 2 → (presentation P w).Group := PresentedGroup.of

def targetLeft : LeftFactor (toUpstream P) →* (presentation P w).Group :=
  Monoid.Coprod.lift (sourceHom P w)
    (FreeGroup.lift ![targetGenerator P w 0, Word.eval (targetGenerator P w) alpha])

def targetRight : RightFactor →* (presentation P w).Group :=
  FreeGroup.lift ![targetGenerator P w 1, Word.eval (targetGenerator P w) beta]

@[simp] theorem targetLeft_a :
    targetLeft P w (aLeft (toUpstream P)) = targetGenerator P w 0 := by
  change FreeGroup.lift ![targetGenerator P w 0, Word.eval (targetGenerator P w) alpha]
    (FreeGroup.of 0) = _
  simp

@[simp] theorem targetLeft_alpha :
    targetLeft P w (alphaLeft (toUpstream P)) = Word.eval (targetGenerator P w) alpha := by
  change FreeGroup.lift ![targetGenerator P w 0, Word.eval (targetGenerator P w) alpha]
    (FreeGroup.of 1) = _
  simp

@[simp] theorem targetLeft_old (g : P.Group) :
    targetLeft P w (oldLeft (toUpstream P) g) = sourceHom P w g := rfl

@[simp] theorem targetLeft_old_generator (i : Fin 2) :
    targetLeft P w (oldLeft (toUpstream P)
      (PresentedGroup.of (rels := (toUpstream P).relSet) i)) =
      Word.eval (targetGenerator P w) (sourceImages i) := by
  change sourceHom P w (PresentedGroup.of i) = _
  exact PresentedGroup.toGroup.of _

theorem target_source_word (v : Word 2) :
    targetLeft P w (oldLeft (toUpstream P) ((toUpstream P).evalWord v)) =
      Word.eval (targetGenerator P w) (Word.subst sourceImages v) := by
  change sourceHom P w (Word.eval PresentedGroup.of v) = _
  rw [Word.map_eval, Word.eval_subst]
  congr 1
  funext i
  simp [sourceHom, targetGenerator]

theorem target_basis (i : UniversalGroup.Gordon.BasisIndex 2) :
    targetLeft P w (leftBasis (toUpstream P) (degreeData P hAb) w i) =
      targetRight P w (rightBasis 2 i) := by
  cases i with
  | conjugateA =>
    simp [leftBasis, rightBasis, targetRight, bRight, alpha, mul_assoc]
  | conjugateAlpha =>
    simp [leftBasis, rightBasis, targetRight, bRight, betaRight, beta, mul_assoc]
  | old i =>
    fin_cases i <;>
      simp [leftBasis, rightBasis, targetRight, bRight, betaRight, rightConjugate,
        sourceImages, sourceB, sourceS, degreeData, mul_assoc]
  | commutator =>
    have hdet : Word.eval (targetGenerator P w) (detector w) = 1 := by
      rw [← detector_row P w]
      exact FP.eval_relator _ _
    simp only [leftBasis, rightBasis, map_mul, map_inv, map_pow, target_source_word,
      targetLeft_alpha]
    simp only [rightConjugate, targetRight, bRight, betaRight, map_mul, map_inv,
      map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply eq_of_mul_inv_eq_one
    simpa [detector, mul_assoc] using hdet

def targetFactor : ∀ s, Factor (toUpstream P) s →* (presentation P w).Group
  | .left => targetLeft P w
  | .right => targetRight P w

theorem target_edge :
    (targetLeft P w).comp (leftMap (toUpstream P) (degreeData P hAb) w) =
      (targetRight P w).comp (rightMap 2) := by
  apply FreeGroup.ext_hom
  intro i
  simpa only [MonoidHom.comp_apply, leftMap, rightMap, FreeGroup.lift_apply_of] using
    target_basis P hAb w i

def reverseWitness : Witness P hAb w →* (presentation P w).Group :=
  Monoid.PushoutI.lift (targetFactor P w)
    ((targetLeft P w).comp (leftMap (toUpstream P) (degreeData P hAb) w)) (by
      intro s
      cases s with
      | left => rfl
      | right => exact (target_edge P hAb w).symm)

theorem reverse_comp_witness :
    (reverseWitness P hAb w).comp (witnessHom P hAb w) = MonoidHom.id _ := by
  apply PresentedGroup.ext
  intro i
  simp only [MonoidHom.comp_apply, witnessHom, PresentedGroup.toGroup.of,
    MonoidHom.id_apply]
  fin_cases i
  · change reverseWitness P hAb w
      (Monoid.PushoutI.of (φ := diagram (toUpstream P) (degreeData P hAb) w) Side.left
        (aLeft (toUpstream P))) = _
    erw [reverseWitness, Monoid.PushoutI.lift_of]
    exact targetLeft_a P w
  · change reverseWitness P hAb w
      (Monoid.PushoutI.of (φ := diagram (toUpstream P) (degreeData P hAb) w) Side.right
        bRight) = _
    erw [reverseWitness, Monoid.PushoutI.lift_of]
    change FreeGroup.lift ![targetGenerator P w 1, Word.eval (targetGenerator P w) beta]
      (FreeGroup.of 0) = _
    exact FreeGroup.lift_apply_of

/-- The exact displayed two-generator output embeds into the attachment amalgam.
The proof checks the four eliminated equations and the remaining detector literally. -/
theorem witnessHom_injective : Function.Injective (witnessHom P hAb w) := by
  intro x y h
  have hx := DFunLike.congr_fun (reverse_comp_witness P hAb w) x
  have hy := DFunLike.congr_fun (reverse_comp_witness P hAb w) y
  exact hx.symm.trans ((congrArg (reverseWitness P hAb w) h).trans hy)

end SmallPresentationStatements.Gordon.UpstreamBridge

namespace SmallPresentationStatements.Gordon

/-- The displayed Gordon output is torsion-free when its source is torsion-free and
its detector word is nontrivial. The only external dependency is the generic amalgam
torsion theorem; the output's embedding and both edge injections are checked. -/
theorem torsionFree {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (hw : ¬ P.wordProblem w) (hT : IsMulTorsionFree P.Group) :
    IsMulTorsionFree (presentation P w).Group := by
  let U := UpstreamBridge.toUpstream P
  let data := UpstreamBridge.degreeData P hAb
  have hw' : U.evalWord w ≠ 1 := by
    rw [UniversalGroup.FP.evalWord_eq_mk]
    exact hw
  have hleft : Function.Injective (UniversalGroup.Gordon.Amalgam.leftMap U data w) :=
    UniversalGroup.Gordon.LeftBridge.leftMap_injective U data w hw'
  have hright : Function.Injective (UniversalGroup.Gordon.Amalgam.rightMap 2) :=
    UniversalGroup.Gordon.amalgam_rightMap_injective 2
  have hdiagram : ∀ s, Function.Injective (UniversalGroup.Gordon.Amalgam.diagram U data w s) := by
    intro s
    cases s with
    | left => exact hleft
    | right => exact hright
  let : IsMulTorsionFree U.Group := hT
  let : IsMulTorsionFree (UniversalGroup.Gordon.Amalgam.LeftFactor U) :=
    ExternalAmalgam.coprod_torsionFree U.Group (FreeGroup (Fin 2))
  let : ∀ s, IsMulTorsionFree (UniversalGroup.Gordon.Amalgam.Factor U s) := by
    intro s
    cases s <;> dsimp [UniversalGroup.Gordon.Amalgam.Factor] <;> infer_instance
  let : Nonempty UniversalGroup.Gordon.Amalgam.Side := ⟨.left⟩
  let : IsMulTorsionFree (UpstreamBridge.Witness P hAb w) :=
    ExternalAmalgam.pushout_torsionFree _ hdiagram
  exact (UpstreamBridge.witnessHom_injective P hAb w).isMulTorsionFree
    (UpstreamBridge.witnessHom P hAb w)

end SmallPresentationStatements.Gordon

