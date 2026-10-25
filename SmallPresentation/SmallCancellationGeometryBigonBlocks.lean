module

public import SmallPresentation.SmallCancellationGeometryBigonWords

/-!
# Relator word blocks under actual bigon suppression

The two affected surviving vertex positions acquire concatenated incidence blocks. Every
based cyclic vertex word is exactly preserved, with no assumption on the alphabet or labels.
-/
@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon

open PermutationCycles

variable {D Y : Type*} {P : RibbonMap D} (B : Bigon P)

/-- Carry complete incidence blocks through the two actual rotation contractions. -/
noncomputable def blocks (block : D → List Y) (d : B.Dart) : List Y :=
  contractBlock B.firstRotation B.secondRemoved
    (contractBlock P.rotation (P.edge B.left) block) (B.dartEquiv d)

/-- No nonempty original block becomes empty under suppression. -/
theorem blocks_nonempty (block : D → List Y) (hblock : ∀ d, block d ≠ []) (d : B.Dart) :
    B.blocks block d ≠ [] :=
  contractBlock_nonempty _ _ _ (contractBlock_nonempty _ _ block hblock) _

open Classical in
/-- Explicit local concatenation: the left side absorbs the right mate, and conversely. -/
theorem blocks_eq (block : D → List Y) (d : B.Dart) :
    B.blocks block d = if d.val = B.left then block d.val ++ block (P.edge B.right)
      else if d.val = B.right then block d.val ++ block (P.edge B.left) else block d.val := by
  classical
  have hfirst : P.rotation d.val = P.edge B.left ↔ d.val = B.right :=
    ⟨fun h ↦ P.rotation.injective (h.trans B.rotation_right.symm),
      fun h ↦ (congrArg P.rotation h).trans B.rotation_right⟩
  have hsecond : B.firstRotation (B.dartEquiv d).val = B.secondRemoved ↔ d.val = B.left :=
    B.firstRotation_eq_second_iff d
  have hmate : P.rotation (P.edge B.right) ≠ P.edge B.left := by
    intro h
    exact P.edge_ne B.right (P.rotation.injective (h.trans B.rotation_right.symm))
  have hdart : (B.dartEquiv d).val.val = d.val := rfl
  have hremoved : B.secondRemoved.val = P.edge B.right := rfl
  dsimp only [blocks, contractBlock]
  simp only [hdart, hremoved, hfirst, hsecond, hmate]
  by_cases hl : d.val = B.left
  · simp [hl, B.left_ne_right]
  · by_cases hr : d.val = B.right <;> simp [hl, hr, B.left_ne_right.symm]

/-- The full based cyclic word survives the actual two-stage rotation contraction. -/
theorem cycle_word [Finite D] (block : D → List Y) (d : B.Dart) :
    (cycleBoundary B.rotation d).flatMap (B.blocks block) =
      (cycleBoundary P.rotation d.val).flatMap block := by
  let σ₂ := contract B.firstRotation B.secondRemoved
  have ht := cycleBoundary_map B.rotation σ₂ B.dartEquiv
    (fun z ↦ by simp [rotation, σ₂]) d
  change (cycleBoundary B.rotation d).flatMap
    (fun z ↦ contractBlock B.firstRotation B.secondRemoved
      (contractBlock P.rotation (P.edge B.left) block) (B.dartEquiv z)) = _
  rw [← List.flatMap_map, ht]
  rw [contract_cycle_word B.firstRotation B.secondRemoved B.second_not_fixed]
  exact contract_cycle_word P.rotation (P.edge B.left) B.first_not_fixed block
    (B.dartEquiv d).val

/-- Reading the actual vertex boundary after suppression gives exactly the original word.
This supports arbitrary incidence alphabets, in particular original relator-position tags. -/
theorem vertex_word [Finite D] (block : D → List Y) (d : B.Dart) :
    (B.suppress.vertexBoundary d).flatMap (B.blocks block) =
      (P.vertexBoundary d.val).flatMap block := by
  simpa only [suppress, RibbonMap.vertexBoundary, cycleBoundary, Equiv.Perm.coe_pow] using
    B.cycle_word block d

/-- In particular, every surviving based vertex retains its original relator word. -/
theorem vertex_word_eq [Finite D] (block : D → List Y) (relator : List Y) (d : B.Dart)
    (h : (P.vertexBoundary d.val).flatMap block = relator) :
    (B.suppress.vertexBoundary d).flatMap (B.blocks block) = relator :=
  (B.vertex_word block d).trans h

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.Bigon
