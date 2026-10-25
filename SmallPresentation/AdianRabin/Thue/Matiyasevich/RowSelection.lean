module

public import SmallPresentation.UniversalGroup.Coding.Thue.RowSelection

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/RowSelection.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.PriorityStage

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Priority
namespace RowSelection

/-!
The row-selection combinatorics behind the displayed identity on page 49.
`selectOdd` keeps positions `1,3,5,...`; iterating it `u` times keeps the
positions congruent to `2^u - 1` modulo `2^u`.
-/

theorem liftBinary_transpose_ends_b {t width : ℕ}
    (rows : Fin t → List (Fin 2))
    (ht : 0 < t) (hwidth : 0 < width)
    (hlen : ∀ i, (rows i).length = width)
    (hend : ∀ i, ∃ init, rows i = init ++ [(1 : Fin 2)]) :
    ∃ init, liftBinary (transpose width rows) = init ++ [b] := by
  obtain ⟨init, hinit⟩ := transpose_ends_b rows ht hwidth hlen hend
  refine ⟨liftBinary init, ?_⟩
  rw [hinit, liftBinary_append]
  simp [liftBinary, liftBit, b]

end RowSelection
end Priority
end Matiyasevich1993
end Thue
end UniversalGroup
