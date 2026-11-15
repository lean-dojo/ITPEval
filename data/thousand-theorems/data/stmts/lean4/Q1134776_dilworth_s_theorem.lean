-- Statement-only formalization of Thousand Theorems artifact Q1134776
-- (thousand-theorems__lean4__Q1134776), "Dilworth's theorem": in a finite
-- partially ordered set, the minimum cardinality of a partition into chains
-- equals the maximum cardinality of an antichain. This file contains no proof.

module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Subset

@[expose] public section

namespace Q1134776

/-- The extended-natural cardinality of a largest antichain for a relation. -/
noncomputable def antichainWidth (α : Type*) (r : α → α → Prop) : ℕ∞ :=
  ⨆ s : {s : Set α // IsAntichain r s}, s.val.encard

/-- A set of sets is a chain partition when each element lies in exactly one member,
and every member is a chain. -/
def IsChainPartition (α : Type*) (r : α → α → Prop) (S : Set (Set α)) :=
  (∀ x : α, ∃! s ∈ S, x ∈ s) ∧ (∀ s ∈ S, IsChain r s)

/-- The minimum extended-natural cardinality of a partition into chains. -/
noncomputable def minChainPartition (α : Type*) (r : α → α → Prop) : ℕ∞ :=
  ⨅ s : {s : Set (Set α) // IsChainPartition α r s}, s.val.encard

/-- Dilworth's theorem for finite partially ordered sets. -/
theorem minChainPartition_eq_antichainWidth
    (α : Type*) [PartialOrder α] [Finite α] :
    minChainPartition α (· ≤ ·) = antichainWidth α (· ≤ ·) := sorry

end Q1134776
