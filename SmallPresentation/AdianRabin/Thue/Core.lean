module

public import SmallPresentation.UniversalGroup.Coding.Thue.Core
public import SmallPresentation.AdianRabin.Computability

/-! The fixed three rows used by the undecidable Thue specialization. -/

@[expose] public section

namespace UniversalGroup.Thue

def baseF (U₃ : List (Fin 2)) : Fin 3 → List (Fin 2) :=
  ![
    [(0 : Fin 2), 0, 1, 0, 1],
    [(0 : Fin 2), 0, 1, 1],
    U₃
  ]

def baseE (V₃ : List (Fin 2)) : Fin 3 → List (Fin 2) :=
  ![
    [(1 : Fin 2), 0, 0],
    [(1 : Fin 2), 0, 0],
    V₃
  ]

def baseSystem (U₃ V₃ : List (Fin 2)) : ThueSystem (Fin 2) :=
  Set.range fun i => (baseF U₃ i, baseE V₃ i)

end UniversalGroup.Thue
