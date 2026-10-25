module

public import SmallPresentation.SmallCancellationGeometryAugmentedLabels
public import SmallPresentation.SmallCancellationDipoleRibbon
public import SmallPresentation.SmallCancellationGeometryCorridorNested

/-!
# Quotient path potentials at relative corners

A potential has equal values at the two ends of each marker arc. Traversing the next
corner multiplies it by the coefficient image. These local laws retain the based-path
information needed for weighted identities, independently of region equations.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

variable {D X H Q : Type*} [Group H] [Group Q] {P : RibbonMap D}

/-- Actual quotient path data for a relative ribbon labelling. -/
structure CornerPotential (L : RibbonLabelling P X H) (q : H →* Q) where
  value : D → Q
  edge : ∀ d, value (P.edge d) = value d
  rotation : ∀ d, value (P.rotation d) = value d * q (L.corner d)

namespace RibbonMap.AugmentedData

variable (L : P.AugmentedData X H) (q : H →* Q) (f : D → Q)
    (he : ∀ d, f (P.edge d) = f d * q (L.coefficient d))
    (hr : ∀ d, f (P.rotation d) = f d * q (L.coefficient d))

/-- Before the leading marker use the original path; the trailing marker follows its coefficient. -/
def potentialValue (d : D × Bool) : Q :=
  if d.2 then f d.1 * q (L.coefficient d.1) else f d.1

include he hr in
/-- Parallel-arc augmentation carries the actual edge and vertex path equations. -/
def cornerPotential : CornerPotential L.labelling q where
  value := L.potentialValue q f
  edge d := by
    rcases d with ⟨d, b⟩
    cases b <;> simp only [RibbonMap.augmented_edge, potentialValue, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, reduceIte, he, L.coefficient_edge, map_inv,
      mul_inv_cancel_right]
  rotation d := by
    rcases d with ⟨d, b⟩
    cases b <;> simp [potentialValue, hr]

end RibbonMap.AugmentedData

namespace BasedRowRibbon

variable {O X Q : Type} [Group Q] {words : O → List (SignedLetter X)}
    {q : FreeGroup X →* Q} (R : BasedRowRibbon words q)

/-- The quotient prefix potential also obeys the cyclic vertex-step law, including wraparound. -/
theorem rotation_potential (d : RowDarts words) :
    rowPotential words q R.base (R.map.rotation d) =
      rowPotential words q R.base d * q (letterValue (rowRead words d)) := by
  rw [R.rotation_eq]
  rcases d with ⟨o, d⟩
  change R.base o * q (prefixValue (words o) (finRotate (words o).length d).val) =
    R.base o * q (prefixValue (words o) d.val) * q (letterValue (words o)[d])
  rw [mul_assoc, ← map_mul, ← prefixValue_succ]
  have hv := PermutationCycles.finRotate_value d
  by_cases hl : d.val + 1 = (words o).length
  · rw [hl, Nat.mod_self] at hv
    rw [hv, hl]
    simp only [prefixValue, List.take_zero, List.take_length, R.row_killed]
    change R.base o * q 1 = R.base o * 1
    rw [map_one]
  · have hlt : d.val + 1 < (words o).length := by omega
    rw [Nat.mod_eq_of_lt hlt] at hv
    rw [hv]

end BasedRowRibbon

end SmallPresentationStatements.RelativeSmallCancellation.Geometry
