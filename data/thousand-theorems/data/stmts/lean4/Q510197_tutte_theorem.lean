-- Statement-only formalization of Thousand Theorems artifact Q510197
-- (thousand-theorems__lean4__Q510197), "Tutte theorem": a finite graph has a
-- perfect matching exactly when deleting any vertex subset leaves no more odd
-- connected components than the subset's cardinality. This file contains no proof.

module

public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Combinatorics.SimpleGraph.UniversalVerts
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex set whose deletion leaves more odd components than its cardinality. -/
def IsTutteViolator (G : SimpleGraph V) (u : Set V) : Prop :=
  u.ncard < ((⊤ : G.Subgraph).deleteVerts u).coe.oddComponents.ncard

variable [Finite V]

/-- Tutte's characterization of finite graphs admitting a perfect matching. -/
theorem tutte : (∃ M : Subgraph G, M.IsPerfectMatching) ↔ ∀ u, ¬G.IsTutteViolator u := sorry

end SimpleGraph
