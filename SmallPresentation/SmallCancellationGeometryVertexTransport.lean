module

public import SmallPresentation.SmallCancellationGeometryRelativeFaces
public import SmallPresentation.SmallCancellationBandPieces

/-! Exact forward and reverse readings under an injective map of vertex rotations. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling

variable {D E X H : Type*} [Finite D] [Group H]
    {P : RibbonMap D} {Q : RibbonMap E} (L : RibbonLabelling P X H)
    (M : RibbonLabelling Q X H) (f : D → E) (hinj : Function.Injective f)
    (hrot : ∀ d, f (P.rotation d) = Q.rotation (f d))
    (harc : ∀ d, M.arc (f d) = L.arc d)
    (hcorner : ∀ d, M.corner (f d) = L.corner d)

omit [Group H] in
include hinj hrot harc hcorner in
/-- A vertex embedding retains the ordered forward word, independently of its edge pairing. -/
theorem vertexWord_map (d : D) : M.vertexWord (f d) = L.vertexWord d := by
  have hh := PermutationCycles.cycleBoundary_map_injective P.rotation Q.rotation f hinj hrot d
  change (P.vertexBoundary d).map f = Q.vertexBoundary (f d) at hh
  rw [vertexWord, vertexWord, ← hh, List.map_map]
  congr 1
  funext e
  simp only [Function.comp_def, harc, hcorner]

include hinj hrot harc hcorner in
/-- The reverse reading also retains the predecessor's inverse coefficient in its exact order. -/
theorem reverseVertexWord_map (d : D) : M.reverseVertexWord (f d) = L.reverseVertexWord d := by
  have hh := PermutationCycles.cycleBoundary_map_injective P.rotation Q.rotation f hinj hrot d
  have hp : Function.minimalPeriod Q.rotation (f d) = Function.minimalPeriod P.rotation d := by
    have hl := congrArg List.length hh
    simpa only [List.length_map, PermutationCycles.cycleBoundary, List.length_ofFn] using hl.symm
  have hs (e : D) : f (P.rotation.symm e) = Q.rotation.symm (f e) := by
    apply Q.rotation.injective
    rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hi (k : ℕ) : f (P.rotation.symm^[k] d) = Q.rotation.symm^[k] (f d) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hs, ih, Function.iterate_succ_apply']
  simp only [reverseVertexWord, hp]
  apply congrArg List.ofFn
  funext k
  rw [← hi, ← hi, harc, hcorner]
  rfl

end SmallPresentationStatements.RelativeSmallCancellation.Geometry.RibbonLabelling
