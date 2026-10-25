module

public import SmallPresentation.UniversalGroup.Coding.Thue.BinaryStage

/-
Ported from `GroupUndecidability/Thue/Matiyasevich/BinaryStage.lean` in 32805433/Adian-Rabin,
commit fb4a401e8fbdba36e7b35c11fde2baa15592e185.
Port: module/public imports/exposed declarations, local import paths, and ite lemma names.
See `provenance.json` for source hashes and any additional API changes.
-/

public import SmallPresentation.AdianRabin.Thue.Matiyasevich.Padding

@[expose] public section

namespace UniversalGroup
namespace Thue
namespace Matiyasevich1993
namespace Binary

/-!
The binary coding stage in Section 2.3 of Matiyasevich (1995).  If the
source alphabet has `N` letters, the (zero-based) form of (18) is

`a_j ↦ a a b^(j+1) a b^(N-j)`.

Thus every codeword has length `N + 4`, begins with the synchronizing marker
`aa`, and ends in `b`.
-/

variable {N r : ℕ}

theorem rho₁_computable (N : ℕ) : Computable (rho₁ N) :=
  (list_flatMap_primrec_of_finite (rho₁Letter N)).to_comp

@[simp] theorem stage₂PrimeF_length (F : Fin r → List (Fin N)) (i : Fin r) :
    (stage₂PrimeF F i).length = (F i).length * (N + 4) := by
  simp [stage₂PrimeF]

@[simp] theorem stage₂PrimeE_length (E : Fin r → List (Fin N)) (i : Fin r) :
    (stage₂PrimeE E i).length = (E i).length * (N + 4) := by
  simp [stage₂PrimeE]

/-- Common source-side lengths become common binary-side lengths. -/
theorem stage₂PrimeF_common_length (F : Fin r → List (Fin N)) (p : ℕ)
    (hF : ∀ i, (F i).length = p) (i : Fin r) :
    (stage₂PrimeF F i).length = p * (N + 4) := by
  simp [hF]

theorem stage₂PrimeE_common_length (E : Fin r → List (Fin N)) (q : ℕ)
    (hE : ∀ i, (E i).length = q) (i : Fin r) :
    (stage₂PrimeE E i).length = q * (N + 4) := by
  simp [hE]
/-- Section 2.3 packaged as an `Embedding`, under the common positive side
length hypotheses supplied by the padding stage. -/
def embedding (F E : Fin r → List (Fin N)) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hF : ∀ i, (F i).length = p) (hE : ∀ i, (E i).length = q) :
    Embedding (finiteSystem F E) (stage₂PrimeSystem F E) where
  encode := rho₁ N
  encode_computable := rho₁_computable N
  thueEq_iff := fun X Y => thueEq_iff F E
    (fun i hnil => by have := hF i; simp [hnil] at this; omega)
    (fun i hnil => by have := hE i; simp [hnil] at this; omega) X Y

end Binary
end Matiyasevich1993
end Thue
end UniversalGroup
