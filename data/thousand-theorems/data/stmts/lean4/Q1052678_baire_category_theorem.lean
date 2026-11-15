-- Statement-only formalization of Thousand Theorems artifact Q1052678
-- (thousand-theorems__lean4__Q1052678), "Baire category theorem": a countable
-- intersection of dense open subsets of a Baire space is dense. This file contains no proof.

module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Constructions

public section

open scoped Topology
open Set TopologicalSpace

variable {X : Type*}

variable [TopologicalSpace X] [BaireSpace X]

/-- The Baire category theorem, formulated using the intersection of a set of sets. -/
theorem dense_sInter_of_isOpen {S : Set (Set X)} (ho : ∀ s ∈ S, IsOpen s)
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := sorry
