-- Statement-only formalization of Thousand Theorems artifact Q1137014
-- (thousand-theorems__lean4__Q1137014), "Tychonoff's theorem": an arbitrary
-- indexed product of compact subsets of topological spaces is compact. This file contains no proof.

module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Data.Set.Accumulate
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Ultrafilter
public import Mathlib.Topology.Defs.Ultrafilter

@[expose] public section

open Set Filter Topology TopologicalSpace Function

variable {ι : Type*}
variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- Tychonoff's theorem: an arbitrary product of compact sets is compact. -/
theorem isCompact_pi_infinite {s : ∀ i, Set (X i)} :
    (∀ i, IsCompact (s i)) → IsCompact { x : ∀ i, X i | ∀ i, x i ∈ s i } := sorry
