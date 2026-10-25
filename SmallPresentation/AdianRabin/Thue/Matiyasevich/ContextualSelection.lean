module

public import SmallPresentation.UniversalGroup.Coding.Thue.ContextualSelection

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/ContextualSelection.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.RowSelection

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Priority
namespace ContextualSelection

open RowSelection

/-!
The contextual form of the row-selection argument on page 50.  The first
priority block only tests whether a letter is `e`; consequently, once its
normal form is clean (a binary word followed by all the `e`'s), an arbitrary
left context acts on the binary suffix by consing binary letters and applying
`selectOdd` once for every `e`.
-/

/-- If a block ending in `1` occurs immediately before a suffix and the whole
word ends in the marker `0`, then that marker belongs to the suffix. -/
theorem split_before_terminal_zero
    {P L S B : List (Fin 2)}
    (hend : ∃ init, L = init ++ [(1 : Fin 2)])
    (hword : P ++ L ++ S = B ++ [(0 : Fin 2)]) :
    ∃ S₀ : List (Fin 2),
      S = S₀ ++ [(0 : Fin 2)] ∧ B = P ++ L ++ S₀ := by
  have hS : S ≠ [] := by
    intro hnil
    subst S
    obtain ⟨init, rfl⟩ := hend
    have hlast := congrArg List.getLast? hword
    simp at hlast
  have hlastS : S.getLast? = some (0 : Fin 2) := by
    calc
      S.getLast? = (P ++ L ++ S).getLast? :=
        (List.getLast?_append_of_ne_nil (P ++ L) hS).symm
      _ = (B ++ [(0 : Fin 2)]).getLast? := congrArg List.getLast? hword
      _ = some 0 := by simp
  obtain ⟨S₀, hS₀⟩ := List.getLast?_eq_some_iff.mp hlastS
  refine ⟨S₀, hS₀, ?_⟩
  have hcancel : (P ++ L ++ S₀) ++ [(0 : Fin 2)] =
      B ++ [(0 : Fin 2)] := by
    simpa [hS₀, List.append_assoc] using hword
  exact (List.append_cancel_right hcancel).symm

/-- Contextual row selection for a long-rule step.  If the normal form of the
left transpose is a clean encoded word, replacing it by any other rectangular
transpose selects the same row index and leaves both binary contexts fixed.

The terminal-`1` hypotheses distinguish the last letter of a selected row
from the terminal `a` (binary `0`) marker in `encode`. -/
theorem replace_transpose_clean (u p q : ℕ)
    (leftRows rightRows : Fin (2 ^ u) → List (Fin 2))
    (hp : ∀ i, (leftRows i).length = p)
    (hq : ∀ i, (rightRows i).length = q)
    (hleftEnd : ∀ i, ∃ init, leftRows i = init ++ [(1 : Fin 2)])
    (_hrightEnd : ∀ i, ∃ init, rightRows i = init ++ [(1 : Fin 2)])
    {l r : List A₂} {B : List (Fin 2)}
    (hl : eCount l = u) (hr : eCount r = 0)
    (hclean : firstNormal
      (l ++ liftBinary (transpose p leftRows) ++ r) = encode u B) :
    ∃ j : Fin (2 ^ u), ∃ left right : List (Fin 2),
      B = left ++ leftRows j ++ right ∧
        firstNormal (l ++ liftBinary (transpose q rightRows) ++ r) =
          encode u (left ++ rightRows j ++ right) := by
  have hclean' : firstNormal (l ++ liftBinary (transpose p leftRows) ++ r) =
      liftBinary (B ++ [(0 : Fin 2)]) ++ List.replicate u e := by
    simpa [encode, liftBinary, liftBit, a, List.append_assoc] using hclean
  obtain ⟨j, before, after, hB, hnormal⟩ :=
    replace_transpose_endpoint u p q leftRows rightRows hp hq hl hr hclean'
  obtain ⟨after₀, hafter, hB₀⟩ := split_before_terminal_zero (hleftEnd j) hB.symm
  refine ⟨j, before, after₀, hB₀, ?_⟩
  simpa [hafter, encode, liftBinary, liftBit, a, List.append_assoc] using hnormal

end ContextualSelection
end Priority
end Matiyasevich1993
end Thue
end UniversalGroup
