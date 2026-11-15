-- Statement-only formalization of Thousand Theorems artifact Q536640
-- (thousand-theorems__lean4__Q536640), "Hall's marriage theorem": a family
-- of finite sets has an injective system of representatives exactly when every
-- finite subfamily satisfies Hall's cardinality condition. This file contains no proof.

module

public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section

open Finset Function

universe u v

namespace Q536640

/-- Hall's marriage theorem for an arbitrarily indexed family of finite sets. -/
theorem hall_s_marriage_theorem {ι : Type u} {α : Type v} [DecidableEq α]
    (t : ι → Finset α) :
    (∀ s : Finset ι, #s ≤ #(s.biUnion t)) ↔
      ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := sorry

end Q536640
