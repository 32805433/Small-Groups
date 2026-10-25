module

public import SmallPresentation.SmallCancellationGeometryRelativeTagged
public import SmallPresentation.SmallCancellationGeometryRelativeBands

/-!
# Recovering original opposite bands from recorded edge blocks

If each based vertex reading is an original vertex boundary and opposite blocks retain
original edge reversal, every current block is an actual consecutive opposite band in the
original ribbon. This replaces a separate peripheral-copy wheel construction.
-/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

variable {D : Type*} (P : RibbonMap D)

theorem vertexBoundary_eq_cons [Finite D] (d : D) : ∃ l, P.vertexBoundary d = d :: l := by
  have hp := Function.minimalPeriod_pos_of_mem_periodicPts (P.rotation.injective.mem_periodicPts d)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [vertexBoundary, hn, List.ofFn_succ]
  exact ⟨_, rfl⟩

end RibbonMap

namespace TaggedRelativeBlockRibbon

variable {D Y X H : Type*} [Finite D] [Group H]
variable {read : Y → SignedLetter X × H} (P : RibbonMap Y)
variable (R : TaggedRelativeBlockRibbon (D := D) Y X H Y read P.vertexBoundary P.edge)

/-- Every block is a prefix of the exact original based vertex boundary. -/
theorem block_prefix (d : D) : R.block d <+: P.vertexBoundary (R.relator d) := by
  obtain ⟨tail, he⟩ := R.map.vertexBoundary_eq_cons d
  refine ⟨tail.flatMap R.block, ?_⟩
  have hw := R.relator_word d
  rwa [he, List.flatMap_cons] at hw

theorem block_length_le (d : D) :
    (R.block d).length ≤ Function.minimalPeriod P.rotation (R.relator d) := by
  simpa using (R.block_prefix P d).length_le

/-- Original tag blocks contain no repeated incidences. -/
theorem block_nodup (d : D) : (R.block d).Nodup :=
  (P.vertexBoundary_nodup _).sublist (R.block_prefix P d).sublist

/-- Every recorded position is the corresponding original vertex iterate. -/
theorem block_getElem (d : D) (k : ℕ) (hk : k < (R.block d).length) :
    (R.block d)[k] = P.rotation^[k] (R.relator d) := by
  rw [(R.block_prefix P d).getElem hk]
  simp [RibbonMap.vertexBoundary, Equiv.Perm.coe_pow]

omit [Finite D] in
@[simp] theorem edge_block_length (d : D) : (R.block (R.map.edge d)).length = (R.block d).length := by
  rw [R.edge_tags]
  simp [Bigon.reverseBlock]

omit [Finite D] in
/-- Exact paired occurrence at the opposite position of the opposite block. -/
theorem edge_block_getElem (d : D) (k : ℕ) (hk : k < (R.block d).length) :
    (R.block (R.map.edge d))[(R.block d).length - 1 - k]'(by rw [R.edge_block_length P]; omega) =
      P.edge ((R.block d)[k]) := by
  simp only [R.edge_tags, Bigon.reverseBlock, List.getElem_map, List.getElem_reverse]
  congr 2
  omega

/-- The lower band end is the reversed-position original vertex iterate. -/
theorem lower_as_iterate (d : D) (k : ℕ) (hk : k < (R.block d).length) :
    P.edge (P.rotation^[k] (R.relator d)) =
      P.rotation^[(R.block d).length - 1 - k] (R.relator (R.map.edge d)) := by
  rw [← R.block_getElem P d k hk, ← R.edge_block_getElem P d k hk]
  apply R.block_getElem P

/-- Recover the actual original opposite band carried by a current compressed edge. -/
def originalBand (d : D) : OppositeBand P (R.block d).length where
  upper k := P.rotation^[k] (R.relator d)
  lower k := P.edge (P.rotation^[k] (R.relator d))
  upper_step k _ := (Function.iterate_succ_apply' P.rotation k (R.relator d)).symm
  lower_step k hk := by
    rw [R.lower_as_iterate P d (k + 1) hk, R.lower_as_iterate P d k (by omega)]
    rw [← Function.iterate_succ_apply' P.rotation
      ((R.block d).length - 1 - (k + 1)) (R.relator (R.map.edge d))]
    congr 2
    omega
  edge_match _ _ := rfl
  upper_injective := by
    intro k l h
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod
      (lt_of_lt_of_le k.isLt (R.block_length_le P d))
      (lt_of_lt_of_le l.isLt (R.block_length_le P d)) h
  lower_injective := by
    intro k l h
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod
      (lt_of_lt_of_le k.isLt (R.block_length_le P d))
      (lt_of_lt_of_le l.isLt (R.block_length_le P d)) (P.edge.injective h)

/-- Every internal original incidence pair retains its coefficient equation throughout
compression. This uses the recorded equation invariant, rather than assuming that an
original face is different from the outside face. -/
theorem originalBand_corner_equations (d : D) (k : ℕ)
    (hk : k + 1 < (R.block d).length) :
    (read ((R.originalBand P d).upper k)).2 *
      (read ((R.originalBand P d).lower (k + 1))).2 = 1 := by
  have hc := (List.isChain_iff_getElem.mp (R.internal_equations d)) k hk
  rw [R.block_getElem P d k (by omega), R.block_getElem P d (k + 1) hk] at hc
  exact hc

end TaggedRelativeBlockRibbon

namespace OppositeBand

variable {D : Type*} {P : RibbonMap D} {n : ℕ} (B : OppositeBand P n)

/-- Taking any consecutive subinterval retains the actual opposite-band laws. -/
def subinterval (start size : ℕ) (h : start + size ≤ n) : OppositeBand P size where
  upper k := B.upper (start + k)
  lower k := B.lower (start + k)
  upper_step k hk := by
    simpa only [Nat.add_assoc] using B.upper_step (start + k) (by omega)
  lower_step k hk := by
    simpa only [Nat.add_assoc] using B.lower_step (start + k) (by omega)
  edge_match k hk := B.edge_match (start + k) (by omega)
  upper_injective := by
    intro k l he
    have hh : (⟨start + k.val, by omega⟩ : Fin n) = ⟨start + l.val, by omega⟩ :=
      B.upper_injective he
    apply Fin.ext
    have := congrArg Fin.val hh
    change start + k.val = start + l.val at this
    omega
  lower_injective := by
    intro k l he
    have hh : (⟨start + k.val, by omega⟩ : Fin n) = ⟨start + l.val, by omega⟩ :=
      B.lower_injective he
    apply Fin.ext
    have := congrArg Fin.val hh
    change start + k.val = start + l.val at this
    omega

end OppositeBand
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
