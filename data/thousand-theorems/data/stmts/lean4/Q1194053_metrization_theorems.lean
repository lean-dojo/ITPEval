-- Statement-only formalization of Thousand Theorems artifact Q1194053
-- (thousand-theorems__lean4__Q1194053), "Metrization theorems": every T3
-- topological space with a second-countable topology is metrizable. This file contains no proof.

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

@[expose] public section

namespace TopologicalSpace

variable (X : Type*) [TopologicalSpace X] [T3Space X] [SecondCountableTopology X]

/-- Urysohn's metrization theorem: a T3 second-countable space is metrizable. -/
instance (priority := 90) metrizableSpace_of_t3_secondCountable : MetrizableSpace X := sorry

end TopologicalSpace
