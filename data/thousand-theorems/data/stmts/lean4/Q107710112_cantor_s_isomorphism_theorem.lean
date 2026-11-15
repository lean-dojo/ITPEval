-- Statement-only formalization of Thousand Theorems artifact Q107710112
-- (thousand-theorems__lean4__Q107710112), "Cantor's isomorphism theorem": any two
-- countable dense nonempty linear orders without endpoints are order isomorphic.
-- This file contains no proof.

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Ideal

@[expose] public section

universe u v

namespace Q107710112

/-- Cantor's isomorphism theorem for countable dense linear orders without endpoints. -/
theorem cantor_isomorphism {α : Type u} {β : Type v}
    [LinearOrder α] [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [LinearOrder β] [Countable β] [DenselyOrdered β] [NoMinOrder β]
    [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) := sorry

end Q107710112
