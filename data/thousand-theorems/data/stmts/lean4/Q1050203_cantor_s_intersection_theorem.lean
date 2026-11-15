-- Statement-only formalization of Thousand Theorems artifact Q1050203
-- (thousand-theorems__lean4__Q1050203), "Cantor's intersection theorem": the total
-- intersection of a nonempty downward-directed family of nonempty compact closed sets is
-- nonempty. This file contains no proof.

module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Data.Set.Accumulate
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Defs.Ultrafilter

@[expose] public section

open Set Filter Topology TopologicalSpace Function

universe u

variable {X : Type u}
variable [TopologicalSpace X]

/-- Cantor's intersection theorem for a set of sets. -/
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) (hSn : ∀ U ∈ S, U.Nonempty)
    (hSc : ∀ U ∈ S, IsCompact U) (hScl : ∀ U ∈ S, IsClosed U) : (⋂₀ S).Nonempty := sorry
