module

public import SmallPresentation.UniversalGroup.Computability.Machine.TM1BinaryAdapter
public import SmallPresentation.AdianRabin.Computability

/-! Computability of binary input encoding, extending the shared machine adapter. -/

@[expose] public section

variable {Γ : Type*} [Inhabited Γ]

namespace UniversalGroup.TM1BinaryAdapter

theorem encodeInput_computable [Primcodable Γ] [Finite Γ] (B : Code Γ) :
    Computable (encodeInput B) :=
  (list_flatMap_primrec_of_finite (fun a : Γ => (B.enc a).toList)).to_comp

end UniversalGroup.TM1BinaryAdapter
