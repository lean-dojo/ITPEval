-- Statement-only formalization of Thousand Theorems artifact Q976607
-- (thousand-theorems__lean4__Q976607), "Erdős–Szekeres theorem": a sufficiently
-- long finite sequence of distinct linearly ordered values has a long increasing
-- subsequence or a long decreasing subsequence. This file contains no proof.

module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

open Function Finset

namespace Q976607

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

/-- The Erdős–Szekeres increasing-or-decreasing subsequence theorem. -/
theorem erdos_szekeres {r s : ℕ} {f : α → β}
    (hn : r * s < Fintype.card α) (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := sorry

end Q976607
