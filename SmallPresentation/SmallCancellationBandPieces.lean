module

public import SmallPresentation.SmallCancellationGeometryRelativeBands

/-!
# Actual augmented band readings imply semi-initial agreement

The two vertex words are read in opposite directions along a band. The bound on the number
of syllables follows from injectivity of the actual dart intervals. Inner face equations give
all internal coefficients; the final positive arc gives only its factor tag. Thus the output
is the exact semi-initial condition used by the metric hypothesis.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation

variable {A I : Type} (G : A → Type) [∀ a, Group (G a)]
variable (length : I → ℕ) [∀ i, NeZero (length i)]
variable (rows : ∀ i, Fin (length i) → Syllable G)

namespace Augmentation

/-- One arc/corner coordinate in the augmented reading of an oriented row. -/
def entry (a : Origin length) (k : ℕ) : Geometry.SignedLetter A × Monoid.CoprodI G :=
  let s := syllableAt G length rows a (k / 2)
  if k % 2 = 0 then ((s.1, true), includeSyllable G s) else ((s.1, false), 1)

/-- The complete based augmented relative word, with two arc incidences per syllable. -/
def word (a : Origin length) : List (Geometry.SignedLetter A × Monoid.CoprodI G) :=
  List.ofFn (fun k : Fin (2 * length a.row) ↦ entry G length rows a k.val)

@[simp] theorem word_length (a : Origin length) : (word G length rows a).length =
    2 * length a.row := List.length_ofFn

@[simp] theorem entry_even (a : Origin length) (t : ℕ) :
    entry G length rows a (2 * t) =
      (((syllableAt G length rows a t).1, true), includeSyllable G (syllableAt G length rows a t)) := by
  simp [entry, Nat.mul_comm 2 t]

@[simp] theorem entry_odd (a : Origin length) (t : ℕ) :
    entry G length rows a (2 * t + 1) = (((syllableAt G length rows a t).1, false), 1) := by
  have hd : (2 * t + 1) / 2 = t := by omega
  simp [entry, hd]

end Augmentation

/-- A factor tag and its actual coefficient image determine the entire tagged syllable. -/
theorem syllable_eq_of_tag_and_value {s t : Syllable G}
    (htag : s.1 = t.1) (hvalue : includeSyllable G s = includeSyllable G t) : s = t := by
  rcases s with ⟨a, x⟩
  rcases t with ⟨b, y⟩
  change a = b at htag
  cases htag
  apply congrArg (Sigma.mk a)
  exact Monoid.CoprodI.of_injective a hvalue

namespace Geometry.RibbonLabelling

variable {D X H : Type*} [Group H] {P : RibbonMap D}

/-- Read the same vertex in reverse direction, starting with the inverse of the chosen arc.
The corner following that reversed arc is the inverse coefficient of its old predecessor. -/
noncomputable def reverseVertexWord (L : RibbonLabelling P X H) (d : D) :
    List (SignedLetter X × H) :=
  List.ofFn (fun k : Fin (Function.minimalPeriod P.rotation d) ↦
    (reverseLetter (L.arc (P.rotation.symm^[k.val] d)),
      (L.corner (P.rotation.symm^[k.val + 1] d))⁻¹))

@[simp] theorem reverseVertexWord_length (L : RibbonLabelling P X H) (d : D) :
    (L.reverseVertexWord d).length = (P.vertexBoundary d).length := by
  simp [reverseVertexWord]

end Geometry.RibbonLabelling

namespace Geometry.OppositeBand

variable {D : Type*} {P : RibbonMap D}
variable (L : RibbonLabelling P A (Monoid.CoprodI G))

theorem forward_reading (d : D) (a : Origin length)
    (hword : L.vertexWord d = Augmentation.word G length rows a)
    (k : ℕ) (hk : k < 2 * length a.row) :
    (L.arc (P.rotation^[k] d), L.corner (P.rotation^[k] d)) =
      Augmentation.entry G length rows a k := by
  have hp : Function.minimalPeriod P.rotation d = 2 * length a.row := by
    simpa [RibbonLabelling.vertexWord] using congrArg List.length hword
  have hh : List.ofFn (fun i : Fin (2 * length a.row) ↦
      (L.arc (P.rotation^[i.val] d), L.corner (P.rotation^[i.val] d))) =
      List.ofFn (fun i : Fin (2 * length a.row) ↦ Augmentation.entry G length rows a i.val) := by
    simpa [RibbonLabelling.vertexWord, RibbonMap.vertexBoundary, List.map_ofFn,
      hp, Augmentation.word, Equiv.Perm.coe_pow, Function.comp_def] using hword
  exact congrFun (List.ofFn_inj.mp hh) ⟨k, hk⟩

theorem reverse_reading (d : D) (a : Origin length)
    (hword : L.reverseVertexWord d = Augmentation.word G length rows a)
    (k : ℕ) (hk : k < 2 * length a.row) :
    (reverseLetter (L.arc (P.rotation.symm^[k] d)),
      (L.corner (P.rotation.symm^[k + 1] d))⁻¹) = Augmentation.entry G length rows a k := by
  have hp : Function.minimalPeriod P.rotation d = 2 * length a.row := by
    simpa using congrArg List.length hword
  have hh : List.ofFn (fun i : Fin (2 * length a.row) ↦
      (reverseLetter (L.arc (P.rotation.symm^[i.val] d)),
        (L.corner (P.rotation.symm^[i.val + 1] d))⁻¹)) =
      List.ofFn (fun i : Fin (2 * length a.row) ↦ Augmentation.entry G length rows a i.val) := by
    simpa [RibbonLabelling.reverseVertexWord, hp, Augmentation.word] using hword
  exact congrFun (List.ofFn_inj.mp hh) ⟨k, hk⟩

/-- An actual embedded opposite band with the displayed augmented row readings supplies
exactly semi-initial agreement. No equality of the final coefficients is required. -/
theorem semiInitial_of_augmented_cornerEquations [Finite D] {m : ℕ}
    (B : OppositeBand P (2 * m - 1))
    (a b : Origin length) (hm : 0 < m)
    (hupper : L.vertexWord (B.upper 0) = Augmentation.word G length rows a)
    (hlower : L.reverseVertexWord (B.lower 0) = Augmentation.word G length rows b)
    (hcorners : ∀ k, k + 1 < 2 * m - 1 →
      L.corner (B.upper k) * L.corner (B.lower (k + 1)) = 1) :
    SemiInitial G length rows a b m := by
  have hupper_length : (P.vertexBoundary (B.upper 0)).length = 2 * length a.row := by
    simpa [RibbonLabelling.vertexWord] using congrArg List.length hupper
  have hlower_length : (P.vertexBoundary (B.lower 0)).length = 2 * length b.row := by
    simpa using congrArg List.length hlower
  have ha : m ≤ length a.row := by
    have h := B.length_le_upper_vertex
    rw [hupper_length] at h
    omega
  have hb : m ≤ length b.row := by
    have h := B.length_le_lower_vertex
    rw [hlower_length] at h
    omega
  have upper_read (t : ℕ) (ht : t < m) :
      (L.arc (B.upper (2 * t)), L.corner (B.upper (2 * t))) =
        (((syllableAt G length rows a t).1, true), includeSyllable G (syllableAt G length rows a t)) := by
    rw [B.upper_iterate (2 * t) (by omega)]
    simpa using forward_reading G length rows L _ a hupper (2 * t) (by omega)
  have lower_arc (t : ℕ) (ht : t < m) :
      reverseLetter (L.arc (B.lower (2 * t))) = ((syllableAt G length rows b t).1, true) := by
    rw [B.lower_iterate (2 * t) (by omega)]
    have h := congrArg Prod.fst (reverse_reading G length rows L _ b hlower (2 * t) (by omega))
    simpa using h
  have tag_eq (t : ℕ) (ht : t < m) :
      (syllableAt G length rows a t).1 = (syllableAt G length rows b t).1 := by
    have h := L.edge_arc (B.upper (2 * t))
    rw [B.edge_match (2 * t) (by omega)] at h
    have hh := congrArg reverseLetter h
    rw [reverseLetter_reverseLetter, lower_arc t ht] at hh
    have hu := congrArg Prod.fst (upper_read t ht)
    change L.arc (B.upper (2 * t)) = ((syllableAt G length rows a t).1, true) at hu
    rw [hu] at hh
    exact (congrArg Prod.fst hh).symm
  refine ⟨hm, ha, hb, ?_, tag_eq (m - 1) (by omega)⟩
  intro t ht
  apply syllable_eq_of_tag_and_value G (tag_eq t (by omega))
  have hc := hcorners (2 * t) (by omega)
  have hu := congrArg Prod.snd (upper_read t (by omega))
  have hl := congrArg Prod.snd
    (reverse_reading G length rows L _ b hlower (2 * t) (by omega))
  simp only [Augmentation.entry_even] at hl
  rw [← B.lower_iterate (2 * t + 1) (by omega)] at hl
  exact hu.symm.trans ((mul_eq_one_iff_eq_inv.mp hc).trans hl)

/-- Inner face equations supply the required internal corner equations for an actual band. -/
theorem semiInitial_of_augmented_readings [Finite D] {m : ℕ} (B : OppositeBand P (2 * m - 1))
    (a b : Origin length) (hm : 0 < m)
    (hupper : L.vertexWord (B.upper 0) = Augmentation.word G length rows a)
    (hlower : L.reverseVertexWord (B.lower 0) = Augmentation.word G length rows b)
    (hregions : ∀ k, k + 1 < 2 * m - 1 → L.faceValue (B.upper k) = 1) :
    SemiInitial G length rows a b m :=
  semiInitial_of_augmented_cornerEquations G length rows L B a b hm hupper hlower
    (fun k hk ↦ B.corner_equation L k hk (hregions k hk))

/-- Preserved internal corner equations suffice for a metric piece even when the band was
obtained by a sequence of compressions and original outside regions must not be reused. -/
theorem piece_of_augmented_cornerEquations [Finite D] {m : ℕ}
    (B : OppositeBand P (2 * m - 1)) (a b : Origin length) (hm : 0 < m) (hne : b ≠ a)
    (hupper : L.vertexWord (B.upper 0) = Augmentation.word G length rows a)
    (hlower : L.reverseVertexWord (B.lower 0) = Augmentation.word G length rows b)
    (hcorners : ∀ k, k + 1 < 2 * m - 1 →
      L.corner (B.upper k) * L.corner (B.lower (k + 1)) = 1) :
    Piece G length rows a m :=
  ⟨b, hne, semiInitial_of_augmented_cornerEquations G length rows L B a b hm hupper hlower hcorners⟩

/-- Distinct indexed origins turn the actual band reading into a metric piece. -/
theorem piece_of_augmented_readings [Finite D] {m : ℕ} (B : OppositeBand P (2 * m - 1))
    (a b : Origin length) (hm : 0 < m) (hne : b ≠ a)
    (hupper : L.vertexWord (B.upper 0) = Augmentation.word G length rows a)
    (hlower : L.reverseVertexWord (B.lower 0) = Augmentation.word G length rows b)
    (hregions : ∀ k, k + 1 < 2 * m - 1 → L.faceValue (B.upper k) = 1) :
    Piece G length rows a m :=
  ⟨b, hne, semiInitial_of_augmented_readings G length rows L B a b hm hupper hlower hregions⟩

end Geometry.OppositeBand

end SmallPresentationStatements.RelativeSmallCancellation
