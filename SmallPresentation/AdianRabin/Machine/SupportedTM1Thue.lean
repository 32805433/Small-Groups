module

public import SmallPresentation.UniversalGroup.Computability.Machine.SupportedTM1Thue
public import SmallPresentation.AdianRabin.Machine.TM1BinaryAdapter

/-! Computable initial words for the shared supported-machine Thue translation. -/

@[expose] public section

namespace UniversalGroup.SupportedTM1Thue

open Turing

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable [Fintype Γ] [Fintype σ]

def binaryStart {Q : Type*} [Inhabited Q] (input : List Bool) :
    List (PostMachine.Symbol (TM0PostAdapter.Phase Q)) :=
  PostMachine.encode (TM0PostAdapter.init input :
    PostMachine.Config (TM0PostAdapter.Phase Q))

theorem binaryStart_computable {Q : Type*} [Inhabited Q] [Finite Q]
    [Primcodable (PostMachine.Symbol (TM0PostAdapter.Phase Q))] :
    Computable (@binaryStart Q inferInstance) := by
  let tape : Bool → PostMachine.Symbol (TM0PostAdapter.Phase Q) :=
    PostMachine.Symbol.tape
  have htape : Computable tape :=
    (Primrec.dom_finite tape).to_comp
  have hhead : Computable fun input : List Bool => tape input.headI :=
    htape.comp Primrec.list_headI.to_comp
  have htail : Computable fun input : List Bool =>
      input.tail.map tape :=
    ((list_map_primrec_of_finite tape).comp Primrec.list_tail).to_comp
  have hprefix : Computable fun input : List Bool =>
      [PostMachine.Symbol.leftMarker, tape input.headI,
        PostMachine.Symbol.state (TM0PostAdapter.Phase.normal (default : Q))] :=
    Computable.list_cons.comp
      (Computable.const PostMachine.Symbol.leftMarker)
      (Computable.list_cons.comp hhead
        (Computable.const
          [PostMachine.Symbol.state
            (TM0PostAdapter.Phase.normal (default : Q))]))
  have hsuffix : Computable fun input : List Bool =>
      input.tail.map tape ++ [PostMachine.Symbol.rightMarker] :=
    Computable.list_append.comp htail
      (Computable.const [PostMachine.Symbol.rightMarker])
  exact (Computable.list_append.comp hprefix hsuffix).of_eq fun input => by
    cases input <;>
      simp [binaryStart, TM0PostAdapter.init, PostMachine.encode,
        PostMachine.encodeTape, tape]

theorem start_computable (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    [Primcodable Γ] [Primcodable (Alphabet B M S)] :
    Computable (start B M S hS) := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact (binaryStart_computable (Q := State B M S)).comp
    (TM1BinaryAdapter.encodeInput_computable B)

end UniversalGroup.SupportedTM1Thue
