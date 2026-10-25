module

public import SmallPresentation.SmallCancellationGeometryRelativeExtractionSystem
public import SmallPresentation.SmallCancellationDipoleRelativeRetainedWords

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry
open PermutationCycles
variable {D X H : Type*} [Finite D] [Group H]
    {P P' : RibbonMap D} {L : RibbonLabelling P X H} {M : RibbonLabelling P' X H}

/-- An unchanged complete vertex remains the same old factor relation, even when
other vertices and labels in the picture are altered. -/
theorem FactorDisc.of_retained {d : D} (F : FactorDisc L d)
    (hr : ∀ e, P.rotation.SameCycle d e → P'.rotation e = P.rotation e)
    (ha : ∀ e, P.rotation.SameCycle d e → M.arc e = L.arc e)
    (hc : ∀ e, P.rotation.SameCycle d e → M.corner e = L.corner e) : FactorDisc M d := by
  have hb := RibbonLabelling.retained_vertexBoundary d hr
  have heq := RibbonLabelling.retained_sameCycle d hr
  constructor
  · intro e he
    rw [ha e ((heq e).mp he), ha d (.refl _ _)]
    exact F.tag e ((heq e).mp he)
  · intro e he
    have hd := (heq e).mp he
    rw [hr e hd, ha e hd, ha _ (Equiv.Perm.sameCycle_apply_right.mpr hd)]
    exact F.alternating e hd
  · intro e he hs
    have hd := (heq e).mp he
    rw [ha e hd] at hs
    rw [hc e hd]
    exact F.negative e hd hs
  · rw [hb]
    convert F.product using 1
    apply congrArg List.prod
    apply List.map_congr_left
    intro e he
    exact hc e ((P.mem_vertexBoundary_iff _ _).mp he)

namespace OldDiscSystem

/-- Turn a rotation-invariant selected family of attaching vertices into proved old
factor discs; all other old vertices retain their original relation and labels. -/
def reclassify (S : OldDiscSystem L) (selected : D → Prop)
    (hbefore : ∀ d, selected (P.rotation d) ↔ selected d)
    (hafter : ∀ d, selected (P'.rotation d) ↔ selected d)
    (hr : ∀ d, ¬selected d → P'.rotation d = P.rotation d)
    (ha : ∀ d, ¬selected d → M.arc d = L.arc d)
    (hc : ∀ d, ¬selected d → M.corner d = L.corner d)
    (hdiscs : ∀ d, selected d → FactorDisc M d) : OldDiscSystem M where
  old d := S.old d ∨ selected d
  invariant d := by
    by_cases hd : selected d
    · exact ⟨fun _ ↦ Or.inr hd, fun _ ↦ Or.inr ((hafter d).mpr hd)⟩
    · rw [or_iff_left hd, or_iff_left (fun h ↦ hd ((hafter d).mp h)), hr d hd]
      exact S.invariant d
  disc d hd := by
    by_cases hs : selected d
    · exact hdiscs d hs
    · have ho : S.old d := hd.resolve_right hs
      have hn (e : D) (he : P.rotation.SameCycle d e) : ¬selected e := by
        intro he'
        exact hs ((P.vertex_predicate_constant selected hbefore he).mpr he')
      exact (S.disc d ho).of_retained
        (fun e he ↦ hr e (hn e he)) (fun e he ↦ ha e (hn e he))
        (fun e he ↦ hc e (hn e he))

end OldDiscSystem
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
