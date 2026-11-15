-- Statement-only formalization of Thousand Theorems artifact Q245098
-- (thousand-theorems__lean4__Q245098), "Intermediate value theorem": a function
-- continuous on a closed interval takes every value in the ordered interval from
-- its value at the left endpoint to its value at the right endpoint. This file contains no proof.

module

public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

open Set

universe u v

namespace Q245098

variable {α : Type u} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [DenselyOrdered α]
variable {δ : Type v} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]

/-- The intermediate value theorem on a closed interval, in the case `f a ≤ t ≤ f b`. -/
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f a) (f b) ⊆ f '' Icc a b := sorry

end Q245098
