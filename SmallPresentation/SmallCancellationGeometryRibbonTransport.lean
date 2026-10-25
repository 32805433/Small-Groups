module

public import SmallPresentation.SmallCancellationGeometryCorridorEndpointsEuler
public import SmallPresentation.SmallCancellationGeometryCornerPotentials

/-! Transport of actual ribbon maps, labels and quotient paths along a dart equivalence. -/

@[expose] public section

namespace SmallPresentationStatements.RelativeSmallCancellation.Geometry

namespace RibbonMap

variable {D E : Type*} (P : RibbonMap D) (e : E ≃ D)

/-- Express the same actual ribbon on a new, bijective coordinate type. -/
def pullback : RibbonMap E where
  edge := e.trans (P.edge.trans e.symm)
  edge_involutive d := by simp only [Equiv.trans_apply, Equiv.apply_symm_apply,
    P.edge_involutive (e d), Equiv.symm_apply_apply]
  edge_ne d := by
    intro h
    have hh := congrArg e h
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at hh
    exact P.edge_ne (e d) hh
  rotation := e.trans (P.rotation.trans e.symm)

@[simp] theorem pullback_edge (d : E) : e ((P.pullback e).edge d) = P.edge (e d) :=
  e.apply_symm_apply _

@[simp] theorem pullback_rotation (d : E) : e ((P.pullback e).rotation d) = P.rotation (e d) :=
  e.apply_symm_apply _

theorem pullback_euler [Finite D] [Finite E] (h : P.EulerEquality) :
    (P.pullback e).EulerEquality :=
  ((P.pullback e).relabel_euler_iff P e (P.pullback_edge e) (P.pullback_rotation e)).mpr h

end RibbonMap

namespace RibbonLabelling

variable {D E X H : Type*} {P : RibbonMap D} (L : RibbonLabelling P X H) (e : E ≃ D)

def pullback : RibbonLabelling (P.pullback e) X H where
  arc d := L.arc (e d)
  corner d := L.corner (e d)
  edge_arc d := by rw [P.pullback_edge]; exact L.edge_arc (e d)

end RibbonLabelling

namespace CornerPotential

variable {D E X H Q : Type*} [Group H] [Group Q] {P : RibbonMap D}
    {L : RibbonLabelling P X H} {q : H →* Q} (F : CornerPotential L q) (e : E ≃ D)

def pullback : CornerPotential (L.pullback e) q where
  value d := F.value (e d)
  edge d := by rw [P.pullback_edge]; exact F.edge (e d)
  rotation d := by rw [P.pullback_rotation]; exact F.rotation (e d)

end CornerPotential
end SmallPresentationStatements.RelativeSmallCancellation.Geometry
