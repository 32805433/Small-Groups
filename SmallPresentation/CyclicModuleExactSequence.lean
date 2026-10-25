module

public import SmallPresentation.CyclicModuleObstruction

/-! Exactness of periodic complexes is preserved by extensions. -/
@[expose] public section

namespace SmallPresentationStatements.CyclicModule.Periodic

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- In an equivariant short exact sequence, even exactness of the outside terms
implies even exactness of the middle term. No splitting is required. -/
theorem evenExact_of_exact_three_term
    (PA : Periodic A) (PB : Periodic B) (PC : Periodic C)
    (i : A →+ B) (p : B →+ C)
    (hi : Function.Injective i) (hker : p.ker = i.range) (hp : Function.Surjective p)
    (hiC : Compatible PA PB i) (hpC : Compatible PB PC p)
    (hA : PA.EvenExact) (hC : PC.EvenExact) : PB.EvenExact := by
  intro b hb
  have hc : PC.difference (p b) = 0 := by rw [← hpC.difference, hb, map_zero]
  obtain ⟨c, hc⟩ := hC (p b) hc
  obtain ⟨v, hv⟩ := hp c
  have hr : b - PB.norm v ∈ i.range := by
    rw [← hker]
    change p (b - PB.norm v) = 0
    rw [map_sub, hpC.norm, hv, hc, sub_self]
  obtain ⟨a, ha⟩ := hr
  have hd : PA.difference a = 0 := by
    apply hi
    rw [hiC.difference, ha, map_sub, hb, PB.difference_norm, sub_self, map_zero]
  obtain ⟨a', ha'⟩ := hA a hd
  refine ⟨v + i a', ?_⟩
  rw [map_add, ← hiC.norm, ha', ha, add_sub_cancel]

/-- The odd statement follows from the same lifting argument with the operators
interchanged. This is useful independently of the torsion application. -/
theorem oddExact_of_exact_three_term
    (PA : Periodic A) (PB : Periodic B) (PC : Periodic C)
    (i : A →+ B) (p : B →+ C)
    (hi : Function.Injective i) (hker : p.ker = i.range) (hp : Function.Surjective p)
    (hiC : Compatible PA PB i) (hpC : Compatible PB PC p)
    (hA : PA.OddExact) (hC : PC.OddExact) : PB.OddExact := by
  intro b hb
  have hc : PC.norm (p b) = 0 := by rw [← hpC.norm, hb, map_zero]
  obtain ⟨c, hc⟩ := hC (p b) hc
  obtain ⟨v, hv⟩ := hp c
  have hr : b - PB.difference v ∈ i.range := by
    rw [← hker]
    change p (b - PB.difference v) = 0
    rw [map_sub, hpC.difference, hv, hc, sub_self]
  obtain ⟨a, ha⟩ := hr
  have hd : PA.norm a = 0 := by
    apply hi
    rw [hiC.norm, ha, map_sub, hb, PB.norm_difference, sub_self, map_zero]
  obtain ⟨a', ha'⟩ := hA a hd
  refine ⟨v + i a', ?_⟩
  rw [map_add, ← hiC.difference, ha', ha, add_sub_cancel]

end SmallPresentationStatements.CyclicModule.Periodic
