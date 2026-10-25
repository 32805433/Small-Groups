module

public import SmallPresentation.SmallCancellationDipoleAugmentedRotation

/-!
# Full augmented readings on literal indexed signed rows

Only the actual canonical vertex rotation and local inverse-marker edge law are required.
Every complete forward and reverse vertex word is computed from the original signed row;
no metric, Euler, region-equation or dipole conclusion is assumed by the adapter.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence

variable {O I A : Type} (length : I → ℕ) [∀ i, NeZero (length i)]
    (G : A → Type) [∀ a, Group (G a)] (rows : ∀ i, Fin (length i) → Syllable G)
    (labels : O → I) (signs : O → Bool)

def arc (d : Darts length labels) : SignedLetter A :=
  ((literalSyllable length G rows (labels d.1) (signs d.1) d.2.1).1, !d.2.2)

def corner (d : Darts length labels) : Monoid.CoprodI G :=
  bif d.2.2 then 1 else includeSyllable G
    (literalSyllable length G rows (labels d.1) (signs d.1) d.2.1)

def origin (d : Darts length labels) : Origin length :=
  bif d.2.2 then negativeOrigin length (labels d.1) (signs d.1) d.2.1
    else positiveOrigin length (labels d.1) (signs d.1) d.2.1

variable (P : RibbonMap (Darts length labels))
    (hedge : ∀ d, arc length G rows labels signs (P.edge d) =
      reverseLetter (arc length G rows labels signs d))

def labelling : RibbonLabelling P A (Monoid.CoprodI G) where
  arc := arc length G rows labels signs
  corner := corner length G rows labels signs
  edge_arc := hedge

variable (hrotation : P.rotation = rotation length labels)
include hrotation

theorem positive_entry (o : O) (k : Fin (length (labels o))) (t : ℕ) :
    ((labelling length G rows labels signs P hedge).arc (P.rotation^[t] ⟨o, k, false⟩),
      (labelling length G rows labels signs P hedge).corner (P.rotation^[t] ⟨o, k, false⟩)) =
      Augmentation.entry G length rows (positiveOrigin length (labels o) (signs o) k) t := by
  rw [hrotation]
  rcases Nat.mod_two_eq_zero_or_one t with hp | hp
  · have ht : t = 2 * (t / 2) := by omega
    rw [ht, rotation_even, Augmentation.entry_even, positive_syllableAt]
    rfl
  · have ht : t = 2 * (t / 2) + 1 := by omega
    rw [ht, rotation_odd_positive, Augmentation.entry_odd, positive_syllableAt]
    rfl

omit hrotation in
theorem include_inverse (s : Syllable G) :
    includeSyllable G (inverseSyllable G s) = (includeSyllable G s)⁻¹ := by
  rcases s with ⟨a, x⟩
  exact map_inv (Monoid.CoprodI.of : G a →* Monoid.CoprodI G) x

theorem negative_entry (o : O) (k : Fin (length (labels o))) (t : ℕ) :
    (reverseLetter ((labelling length G rows labels signs P hedge).arc
        (P.rotation.symm^[t] ⟨o, k, true⟩)),
      ((labelling length G rows labels signs P hedge).corner
        (P.rotation.symm^[t + 1] ⟨o, k, true⟩))⁻¹) =
      Augmentation.entry G length rows (negativeOrigin length (labels o) (signs o) k) t := by
  rw [hrotation]
  rcases Nat.mod_two_eq_zero_or_one t with hp | hp
  · have ht : t = 2 * (t / 2) := by omega
    rw [ht, reverse_rotation_even, reverse_rotation_odd_negative, Augmentation.entry_even,
      negative_syllableAt, include_inverse]
    rfl
  · have ht : t = 2 * (t / 2) + 1 := by omega
    have hnext : t + 1 = 2 * (t / 2 + 1) := by omega
    rw [hnext, reverse_rotation_even, ht, reverse_rotation_odd_negative, Augmentation.entry_odd,
      negative_syllableAt]
    change ((_, false), (1 : Monoid.CoprodI G)⁻¹) = ((_, false), 1)
    rw [inv_one]
    rfl

theorem positive_vertexWord (o : O) (k : Fin (length (labels o))) :
    (labelling length G rows labels signs P hedge).vertexWord ⟨o, k, false⟩ =
      Augmentation.word G length rows (positiveOrigin length (labels o) (signs o) k) := by
  have hp : Function.minimalPeriod P.rotation ⟨o, k, false⟩ = 2 * length (labels o) := by
    rw [hrotation]
    exact period length labels o k false
  simp only [RibbonLabelling.vertexWord, RibbonMap.vertexBoundary, hp, List.map_ofFn,
    Equiv.Perm.coe_pow, Augmentation.word]
  apply List.ofFn_inj.mpr
  funext t
  exact positive_entry length G rows labels signs P hedge hrotation o k t.val

theorem negative_vertexWord (o : O) (k : Fin (length (labels o))) :
    (labelling length G rows labels signs P hedge).reverseVertexWord ⟨o, k, true⟩ =
      Augmentation.word G length rows (negativeOrigin length (labels o) (signs o) k) := by
  have hp : Function.minimalPeriod P.rotation ⟨o, k, true⟩ = 2 * length (labels o) := by
    rw [hrotation]
    exact period length labels o k true
  simp only [RibbonLabelling.reverseVertexWord, hp, Augmentation.word]
  apply List.ofFn_inj.mpr
  funext t
  exact negative_entry length G rows labels signs P hedge hrotation o k t.val

/-- All complete indexed oriented readings are proved from the literal local labels. -/
def readings : AugmentedReadings G length rows P (labelling length G rows labels signs P hedge) where
  origin := origin length labels signs
  forward := by
    rintro ⟨o, k, b⟩ h
    cases b with
    | false => exact positive_vertexWord length G rows labels signs P hedge hrotation o k
    | true => contradiction
  backward := by
    rintro ⟨o, k, b⟩ h
    cases b with
    | false => contradiction
    | true => exact negative_vertexWord length G rows labels signs P hedge hrotation o k

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.AugmentedOccurrence
