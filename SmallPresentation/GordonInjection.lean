module

public import SmallPresentation.Gordon
public import SmallPresentation.AdianRabin.Gordon.Embedding

/-!
# Injectivity of the Gordon source map

This adapts the pinned upstream rank-five free-basis proof to the exact
two-generator words in `GordonWords`. The torsion theorem for the amalgam is
a separate obligation.
-/
@[expose] public section

namespace SmallPresentationStatements.Gordon.UpstreamBridge

def toUpstream {n m : ℕ} (P : FP n m) : UniversalGroup.FP n m := ⟨P.relator⟩

def degreeData {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) :
    UniversalGroup.Gordon.TorsionData (toUpstream P) where
  p := 1
  selected := ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  q := fun _ ↦ 1
  gcd_q := by simp
  exactOrder := by intro i; simpa [hAb]
  degree := fun i ↦ 2 * i.val + 1
  degree_pos := by intro i; omega
  degree_injective := by
    intro i j h
    change 2 * i.val + 1 = 2 * j.val + 1 at h
    apply Fin.ext
    omega
  degree_selected := by intro i; rfl

theorem alpha_eq : UniversalGroup.Gordon.alphaWord = alpha := by
  simp [UniversalGroup.Gordon.alphaWord, UniversalGroup.Gordon.aWord,
    UniversalGroup.Gordon.bWord, UniversalGroup.Word.product,
    UniversalGroup.Word.generator, UniversalGroup.Word.inverse,
    UniversalGroup.Word.pow, alpha, Word.gen, Word.inverse, Word.power]

theorem beta_eq : UniversalGroup.Gordon.betaWord = beta := by
  simp [UniversalGroup.Gordon.betaWord, UniversalGroup.Gordon.aWord,
    UniversalGroup.Gordon.bWord, UniversalGroup.Word.product,
    UniversalGroup.Word.generator, UniversalGroup.Word.inverse,
    alpha_eq, beta, Word.gen, Word.inverse, List.append_assoc]

theorem encodedGenerator_eq {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (i : Fin 2) :
    UniversalGroup.Gordon.encodedGenerator (degreeData P hAb) i = sourceImages i := by
  fin_cases i <;>
    simp [UniversalGroup.Gordon.encodedGenerator, UniversalGroup.Gordon.rightConjugateWord,
      UniversalGroup.Gordon.aWord, UniversalGroup.Gordon.bWord,
      UniversalGroup.Word.product, UniversalGroup.Word.pow, UniversalGroup.Word.inverse,
      UniversalGroup.Word.generator, alpha_eq, beta_eq, degreeData,
      sourceImages, sourceB, sourceS, Word.gen, Word.power, Word.inverse, List.append_assoc]

theorem eval_encodedGenerator {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    {H : Type*} [Group H] (x : Fin 2 → H) (i : Fin 2) :
    UniversalGroup.Word.eval x
      (UniversalGroup.Gordon.encodedGenerator (degreeData P hAb) i) =
      Word.eval x (sourceImages i) := by
  rw [encodedGenerator_eq]
  rfl

theorem encodeWord_eq {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :
    UniversalGroup.Gordon.encodeWord (degreeData P hAb) w = Word.subst sourceImages w := by
  unfold UniversalGroup.Gordon.encodeWord
  rw [funext (encodedGenerator_eq P hAb)]
  rfl

theorem additionalRelator_eq {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :
    UniversalGroup.Gordon.additionalRelator (degreeData P hAb) w = detector w := by
  simp [UniversalGroup.Gordon.additionalRelator, UniversalGroup.Word.relation,
    UniversalGroup.Gordon.paperCommutator, UniversalGroup.Gordon.rightConjugateWord,
    UniversalGroup.Gordon.bWord, UniversalGroup.Word.product, UniversalGroup.Word.mul,
    UniversalGroup.Word.inverse, UniversalGroup.Word.pow, UniversalGroup.Word.generator,
    alpha_eq, beta_eq, encodeWord_eq, detector, Word.inverse, Word.power, Word.gen,
    List.map_map, List.append_assoc, Function.comp_def]

abbrev Witness {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :=
  UniversalGroup.Gordon.Amalgam.Pushout (toUpstream P) (degreeData P hAb) w

def witnessGenerator {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :
    Fin 2 → Witness P hAb w :=
  UniversalGroup.Gordon.Amalgam.witnessGenerator (toUpstream P) (degreeData P hAb) w

theorem witness_source_word {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w v : Word 2) :
    Word.eval (witnessGenerator P hAb w) (Word.subst sourceImages v) =
      UniversalGroup.Gordon.Amalgam.pushLeft (toUpstream P) (degreeData P hAb) w
        (UniversalGroup.Gordon.Amalgam.oldLeft (toUpstream P)
          ((toUpstream P).evalWord v)) := by
  rw [← encodeWord_eq P hAb v]
  exact UniversalGroup.Gordon.Amalgam.eval_encodeWord_witness _ _ _ _

theorem witness_relator {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (i : Fin (m + 1)) :
    Word.eval (witnessGenerator P hAb w) ((presentation P w).relator i) = 1 := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [detector_row, ← additionalRelator_eq P hAb w]
    exact UniversalGroup.Gordon.Amalgam.eval_additional _ _ _
  · rw [source_row, witness_source_word]
    change UniversalGroup.Gordon.Amalgam.pushLeft _ _ _
      (UniversalGroup.Gordon.Amalgam.oldLeft _ ((toUpstream P).evalWord
        ((toUpstream P).relator j))) = 1
    rw [UniversalGroup.FP.relator_eq_one, map_one, map_one]

def witnessHom {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :
    (presentation P w).Group →* Witness P hAb w :=
  PresentedGroup.toGroup (f := witnessGenerator P hAb w) (by
    rintro _ ⟨i, rfl⟩
    exact witness_relator P hAb w i)

theorem witness_comp_source {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1) (w : Word 2) :
    (witnessHom P hAb w).comp (sourceHom P w) =
      (UniversalGroup.Gordon.Amalgam.pushLeft (toUpstream P) (degreeData P hAb) w).comp
        (UniversalGroup.Gordon.Amalgam.oldLeft (toUpstream P)) := by
  ext i
  simp only [MonoidHom.comp_apply, sourceHom, PresentedGroup.toGroup.of]
  rw [Word.map_eval]
  have hf : (fun j ↦ witnessHom P hAb w (PresentedGroup.of j)) =
      witnessGenerator P hAb w := by
    funext j
    exact PresentedGroup.toGroup.of _
  rw [hf, ← eval_encodedGenerator P hAb]
  exact UniversalGroup.Gordon.Amalgam.eval_encodedGenerator_witness _ _ _ _

end SmallPresentationStatements.Gordon.UpstreamBridge

namespace SmallPresentationStatements.Gordon

/-- Gordon's rank-five free bases detect every element of the original source group. -/
theorem sourceHom_injective {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (hw : ¬ P.wordProblem w) : Function.Injective (sourceHom P w) := by
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
  have hpush : Function.Injective (UniversalGroup.Gordon.Amalgam.pushLeft U data w) :=
    Monoid.PushoutI.of_injective hdiagram UniversalGroup.Gordon.Amalgam.Side.left
  have hcomp : Function.Injective
      ((UpstreamBridge.witnessHom P hAb w).comp (sourceHom P w)) := by
    rw [UpstreamBridge.witness_comp_source]
    exact hpush.comp Monoid.Coprod.inl_injective
  intro a b h
  apply hcomp
  exact congrArg (UpstreamBridge.witnessHom P hAb w) h

theorem exists_embedding {m : ℕ} (P : FP 2 m)
    (hAb : Abelianization.of (PresentedGroup.of (rels := P.relSet) 0) = 1)
    (w : Word 2) (hw : ¬ P.wordProblem w) :
    ∃ f : P.Group →* (presentation P w).Group, Function.Injective f :=
  ⟨sourceHom P w, sourceHom_injective P hAb w hw⟩

end SmallPresentationStatements.Gordon
