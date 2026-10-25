module

public import SmallPresentation.SmallCancellationDipolePairFactorReplacement
public import SmallPresentation.SmallCancellationGeometryMarkedPictureCounts

/-! Exact retained and omitted vertex cycles in inverse-row replacement. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks.ReplacementData
open PermutationCycles

variable {D X H : Type*} [Finite D] [Group H] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {n : ℕ} (T : ReplacementData P L n)

/-- Original vertices meeting the selected inverse pair lie entirely in its coordinate image. -/
theorem range_cycle {d e : D} (hd : d ∈ Set.range T.embedding)
    (hde : P.rotation.SameCycle d e) : e ∈ Set.range T.embedding :=
  embedding_range_cycle_closed P.rotation (source n) T.embedding T.rotation hd hde

/-- Exact cycle equality outside both replaced vertices, including cycles of a retained boundary. -/
theorem sameCycle_outside (d : D) (hd : d ∉ Set.range T.embedding) (e : D) :
    T.map.rotation.SameCycle d e ↔ P.rotation.SameCycle d e := by
  apply sameCycle_iff_of_cycle_agreement
  intro x hx
  exact T.rotation_outside x (fun hm ↦ hd (T.range_cycle hm hx.symm))

/-- No surviving outside attaching vertex belongs to either removed attaching cycle. -/
theorem selected_not_sameCycle_outside (k : Dart n) (d : D)
    (hd : d ∉ Set.range T.embedding) : ¬P.rotation.SameCycle (T.embedding k) d :=
  fun h ↦ hd (T.range_cycle ⟨k,rfl⟩ h)

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.PairFactorBlocks.ReplacementData
