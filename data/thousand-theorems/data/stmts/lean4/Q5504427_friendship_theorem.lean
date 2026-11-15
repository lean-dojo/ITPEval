-- Statement-only formalization of Thousand Theorems artifact Q5504427
-- (thousand-theorems__lean4__Q5504427), "Friendship theorem": every finite nonempty
-- simple graph in which each pair of distinct vertices has exactly one common neighbor
-- has a vertex adjacent to every other distinct vertex. This file contains no proof.

module

public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace Theorems100

universe u

variable {V : Type u}

variable (G : SimpleGraph V)

open scoped Classical in
/-- A friendship graph has exactly one common neighbor for every pair of distinct vertices. -/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A politician is a vertex adjacent to every other distinct vertex. -/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

variable [Fintype V] {G : SimpleGraph V}

/-- Every finite nonempty friendship graph has a politician. -/
theorem friendship_theorem (hG : Friendship G) [Nonempty V] : ExistsPolitician G := sorry

end Theorems100
