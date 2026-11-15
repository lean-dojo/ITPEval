-- Statement-only formalization of Thousand Theorems artifact Q420714
-- (thousand-theorems__lean4__Q420714), "Akra-Bazzi theorem": a divide-and-conquer
-- recurrence is asymptotically bounded above by its Akra-Bazzi bound.
-- This file contains no proof.

module

public import Mathlib.Computability.AkraBazzi.SumTransform

@[expose] public section

open Filter Asymptotics

namespace Q420714

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ}
  {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)

include R

/-- The upper-bound part of the Akra-Bazzi theorem. -/
theorem isBigO_asympBound :
    T =O[atTop] AkraBazziRecurrence.asympBound g a b := sorry

end Q420714
