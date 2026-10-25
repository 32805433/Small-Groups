module

public import SmallPresentation.SmallCancellationDipoleAugmentedReadings
public import SmallPresentation.SmallCancellationGeometryCornerPotentials

/-!
# Quotient weights of actual relative indexed dipoles

The corner potential determines the original marked quotient basepoint multiplied by the
literal coefficient prefix. At a matched positive/negative marker edge, the reverse-prefix
identity for the opposite signed row forces equality of those original quotient basepoints.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A Q : Type} [Group Q] (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)

def coefficientWord (i : I) (sign : Bool) : List (Monoid.CoprodI G) :=
  List.ofFn (fun k : Fin (length i) ↦ includeSyllable G (literalSyllable length G rows i sign k))

omit [∀ i, NeZero (length i)] in
@[simp] theorem coefficientWord_length (i : I) (sign : Bool) :
    (coefficientWord length G rows i sign).length = length i := List.length_ofFn

def coefficientPrefix (i : I) (sign : Bool) (n : ℕ) : Monoid.CoprodI G :=
  ((coefficientWord length G rows i sign).take n).prod

omit [∀ i, NeZero (length i)] in
theorem coefficientPrefix_succ (i : I) (sign : Bool) (k : Fin (length i)) :
    coefficientPrefix length G rows i sign (k.val + 1) =
      coefficientPrefix length G rows i sign k.val *
        includeSyllable G (literalSyllable length G rows i sign k) := by
  have hk : k.val < (coefficientWord length G rows i sign).length := by simp
  unfold coefficientPrefix
  rw [← List.take_append_getElem hk, List.prod_append]
  simp [coefficientWord]

omit [∀ i, NeZero (length i)] in
theorem literalSyllable_not (i : I) (sign : Bool) (k : Fin (length i)) :
    literalSyllable length G rows i (!sign) k =
      inverseSyllable G (literalSyllable length G rows i sign k.rev) := by
  cases sign with
  | true => rfl
  | false =>
    simp only [Bool.not_false, literalSyllable, Bool.cond_true, Bool.cond_false, Fin.rev_rev]
    rcases rows i k with ⟨a, x⟩
    exact congrArg (Sigma.mk a) (inv_inv x).symm

omit [∀ i, NeZero (length i)] in
theorem coefficientWord_not (i : I) (sign : Bool) :
    coefficientWord length G rows i (!sign) =
      ((coefficientWord length G rows i sign).map Inv.inv).reverse := by
  apply List.ext_getElem
  · simp
  · intro n hn hm
    have hn' : n < length i := by simpa using hn
    have hh := congrArg (includeSyllable G)
      (literalSyllable_not length G rows i sign ⟨n, hn'⟩)
    rw [include_inverse] at hh
    simpa only [coefficientWord, List.getElem_ofFn, List.getElem_reverse, List.getElem_map,
      List.length_map, List.length_ofFn, Fin.rev, Nat.sub_sub, Nat.add_comm] using hh

/-- In any quotient killing a whole word, an inverse prefix equals its complementary prefix. -/
theorem inverse_coefficient_prefix {H : Type} [Group H] (q : H →* Q)
    (w : List H) (hw : q w.prod = 1) (n : ℕ) :
    q ((((w.map Inv.inv).reverse).take n).prod) = q ((w.take (w.length - n)).prod) := by
  rw [List.take_reverse, List.length_map, ← List.map_drop, ← List.prod_inv_reverse, map_inv]
  have hh : q ((w.take (w.length - n)).prod) * q ((w.drop (w.length - n)).prod) = 1 := by
    rw [← map_mul, ← List.prod_append, List.take_append_drop]
    exact hw
  exact (mul_eq_one_iff_eq_inv.mp hh).symm

omit [∀ i, NeZero (length i)] in
theorem coefficientPrefix_not (q : Monoid.CoprodI G →* Q) (i : I) (sign : Bool)
    (hkill : q (coefficientWord length G rows i sign).prod = 1) (n : ℕ) :
    q (coefficientPrefix length G rows i (!sign) n) =
      q (coefficientPrefix length G rows i sign (length i - n)) := by
  unfold coefficientPrefix
  rw [coefficientWord_not, inverse_coefficient_prefix q _ hkill, coefficientWord_length]

variable (labels : O → I) (signs : O → Bool) (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))
    (hrotation : P.rotation = rotation length labels) (q : Monoid.CoprodI G →* Q)
    (F : CornerPotential (labelling length G rows labels signs P hedge) q)

/-- The potential at the original marked leading corner of each occurrence. -/
def quotientBase (o : O) : Q := F.value ⟨o, 0, false⟩

include hrotation in
theorem positive_step (o : O) (k : Fin (length (labels o))) :
    F.value ⟨o, k + 1, false⟩ = F.value ⟨o, k, false⟩ *
      q (includeSyllable G (literalSyllable length G rows (labels o) (signs o) k)) := by
  have h₁ := F.rotation ⟨o, k, false⟩
  have h₂ := F.rotation ⟨o, k, true⟩
  rw [hrotation] at h₁ h₂
  change F.value ⟨o, k, true⟩ = F.value ⟨o, k, false⟩ * _ at h₁
  change F.value ⟨o, k + 1, false⟩ = F.value ⟨o, k, true⟩ * q 1 at h₂
  rw [map_one, mul_one, h₁] at h₂
  exact h₂

include hrotation in
theorem positive_value (o : O) (k : Fin (length (labels o))) :
    F.value ⟨o, k, false⟩ = quotientBase length G rows labels signs P hedge q F o *
      q (coefficientPrefix length G rows (labels o) (signs o) k.val) := by
  suffices ∀ (n : ℕ) (hn : n < length (labels o)),
      F.value ⟨o, ⟨n, hn⟩, false⟩ = quotientBase length G rows labels signs P hedge q F o *
        q (coefficientPrefix length G rows (labels o) (signs o) n) from this k.val k.isLt
  intro n
  induction n with
  | zero => intro hn; simp [quotientBase, coefficientPrefix]
  | succ n ih =>
    intro hn
    let k : Fin (length (labels o)) := ⟨n, by omega⟩
    have hk : k + 1 = (⟨n + 1, hn⟩ : Fin (length (labels o))) := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt' hn
    have hs := positive_step length G rows labels signs P hedge hrotation q F o k
    rw [hk, ih k.isLt] at hs
    rw [coefficientPrefix_succ length G rows (labels o) (signs o) k, map_mul, ← mul_assoc]
    exact hs

include hrotation in
theorem negative_value (o : O) (k : Fin (length (labels o))) :
    F.value ⟨o, k, true⟩ = quotientBase length G rows labels signs P hedge q F o *
      q (coefficientPrefix length G rows (labels o) (signs o) (k.val + 1)) := by
  have hh := F.rotation ⟨o, k, false⟩
  rw [hrotation] at hh
  change F.value ⟨o, k, true⟩ = F.value ⟨o, k, false⟩ *
    q (includeSyllable G (literalSyllable length G rows (labels o) (signs o) k)) at hh
  rw [positive_value length G rows labels signs P hedge hrotation q F] at hh
  rw [coefficientPrefix_succ, map_mul, ← mul_assoc]
  exact hh

include hrotation F in
/-- The local cyclic potential law itself proves that the full coefficient row dies in the quotient. -/
theorem coefficient_row_killed (o : O) :
    q (coefficientWord length G rows (labels o) (signs o)).prod = 1 := by
  have hn : 0 < length (labels o) := NeZero.pos _
  let k : Fin (length (labels o)) := ⟨length (labels o) - 1, by omega⟩
  have hk : k.val + 1 = length (labels o) := by dsimp [k]; omega
  have hz : k + 1 = 0 := by
    apply Fin.ext
    rw [← finRotate_apply, PermutationCycles.finRotate_value, hk, Nat.mod_self]
    rfl
  have hh := positive_step length G rows labels signs P hedge hrotation q F o k
  rw [hz, positive_value length G rows labels signs P hedge hrotation q F o k] at hh
  rw [mul_assoc, ← map_mul, ← coefficientPrefix_succ, hk] at hh
  have hfull : coefficientPrefix length G rows (labels o) (signs o) (length (labels o)) =
      (coefficientWord length G rows (labels o) (signs o)).prod := by
    unfold coefficientPrefix
    rw [← coefficientWord_length length G rows (labels o) (signs o), List.take_length]
  rw [hfull] at hh
  apply mul_left_cancel (a := quotientBase length G rows labels signs P hedge q F o)
  exact hh.symm.trans (mul_one _).symm

include hrotation in
/-- The actual edge between aligned inverse relative rows forces equal original quotient bases. -/
theorem matched_base_eq (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (he : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    quotientBase length G rows labels signs P hedge q F first =
      quotientBase length G rows labels signs P hedge q F second := by
  have hh := F.edge ⟨first, k, false⟩
  rw [he, negative_value length G rows labels signs P hedge hrotation q F,
    positive_value length G rows labels signs P hedge hrotation q F] at hh
  have hrow := congrArg (fun i ↦ q (coefficientPrefix length G rows i (signs second)
    (l.val + 1))) hlabel.symm
  rw [hrow, hsign, coefficientPrefix_not length G rows q _ _
    (coefficient_row_killed length G rows labels signs P hedge hrotation q F first)] at hh
  have hp : length (labels first) - (l.val + 1) = k.val := by omega
  rw [hp] at hh
  exact (mul_right_cancel hh).symm

include hrotation in
/-- Every corresponding pair has equal quotient potentials once its two row bases agree. -/
theorem matched_marker_values (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (hbase : quotientBase length G rows labels signs P hedge q F first =
      quotientBase length G rows labels signs P hedge q F second) :
    F.value ⟨first, k, false⟩ = F.value ⟨second, l, true⟩ := by
  rw [positive_value length G rows labels signs P hedge hrotation q F,
    negative_value length G rows labels signs P hedge hrotation q F, ← hbase]
  have hrow := congrArg (fun i ↦ q (coefficientPrefix length G rows i (signs second)
    (l.val + 1))) hlabel.symm
  rw [hrow, hsign, coefficientPrefix_not length G rows q _ _
    (coefficient_row_killed length G rows labels signs P hedge hrotation q F first)]
  congr 3
  omega

include hrotation in
/-- Both marker phases of every opposite incidence pair have equal quotient potentials. -/
theorem matched_all_marker_values (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (hbase : quotientBase length G rows labels signs P hedge q F first =
      quotientBase length G rows labels signs P hedge q F second) (b : Bool) :
    F.value ⟨first, k, b⟩ = F.value ⟨second, l, !b⟩ := by
  cases b with
  | false =>
    exact matched_marker_values length G rows labels signs P hedge hrotation q F
      first second k l hlabel hsign hposition hbase
  | true =>
    have hs : signs first = !signs second := by rw [hsign, Bool.not_not]
    have hp : l.val + k.val + 1 = length (labels second) := by
      have hl := congrArg length hlabel
      omega
    exact (matched_marker_values length G rows labels signs P hedge hrotation q F
      second first l k hlabel.symm hs hp hbase.symm).symm

open RelationCoordinates in
/-- The selected original quotient-based signed contribution. -/
def relativeWeight {J : Type} (select : I → Option J) (o : O) :
    Weighted.Coordinates (Q := Q) (J := J) :=
  Peiffer.weight (MonoidHom.id Q) select
    ((quotientBase length G rows labels signs P hedge q F o, labels o), signs o)

include hrotation in
/-- The actual relative dipole removes zero total original quotient weight. -/
theorem matched_weight_cancel {J : Type} (select : I → Option J) (first second : O)
    (k : Fin (length (labels first))) (l : Fin (length (labels second)))
    (hlabel : labels first = labels second) (hsign : signs second = !signs first)
    (hposition : k.val + l.val + 1 = length (labels first))
    (he : P.edge ⟨first, k, false⟩ = ⟨second, l, true⟩) :
    relativeWeight length G rows labels signs P hedge q F select first +
      relativeWeight length G rows labels signs P hedge q F select second = 0 := by
  have hb := matched_base_eq length G rows labels signs P hedge hrotation q F
    first second k l hlabel hsign hposition he
  simp only [relativeWeight, RelationCoordinates.Peiffer.weight, MonoidHom.id_apply,
    ← hlabel, hsign, ← hb]
  cases signs first <;> simp

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
