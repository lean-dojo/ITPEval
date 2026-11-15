-- Statement-only formalization of Thousand Theorems artifact Q4950096
-- (thousand-theorems__lean4__Q4950096), "Bourbaki–Witt theorem": every inflationary
-- self-map of a nonempty chain-complete partial order has a fixed point.
-- This file contains no proof.

module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Preorder.Chain

@[expose] public section

namespace Q4950096

variable {α : Type*}

/-- A nonempty chain in an ordered type. -/
structure NonemptyChain (α : Type*) [LE α] where
  carrier : Set α
  nonempty' : carrier.Nonempty
  isChain' : IsChain (· ≤ ·) carrier

/-- A partial order in which every nonempty chain has a least upper bound. -/
class ChainCompletePartialOrder (α : Type*) extends PartialOrder α where
  cSup : NonemptyChain α → α
  le_cSup (c : NonemptyChain α) (x : α) : x ∈ c.carrier → x ≤ cSup c
  cSup_le (c : NonemptyChain α) (x : α) : (∀ y ∈ c.carrier, y ≤ x) → cSup c ≤ x

open Function

/-- The Bourbaki-Witt fixed-point theorem for inflationary endomaps. -/
theorem nonempty_fixedPoints_of_inflationary [ChainCompletePartialOrder α] [Nonempty α]
    {f : α → α} (le_map : ∀ x, x ≤ f x) : (fixedPoints f).Nonempty := sorry

end Q4950096
