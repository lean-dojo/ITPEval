-- Statement-only formalization of Thousand Theorems artifact Q1077462
-- (thousand-theorems__lean4__Q1077462), "König's theorem (set theory)":
-- if every cardinal in one indexed family is strictly smaller than its counterpart,
-- then the indexed cardinal sum is strictly smaller than the indexed cardinal product.
-- This file contains no proof.

module

public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

universe u v

namespace Q1077462

/-- König's theorem for indexed families of cardinals. -/
theorem koenig_sum_lt_prod {ι : Type u} (f g : ι → Cardinal.{v})
    (H : ∀ i, f i < g i) : Cardinal.sum f < Cardinal.prod g := sorry

end Q1077462
