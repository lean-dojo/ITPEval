-- Statement-only formalization of Thousand Theorems artifact Q3527102
-- (thousand-theorems__lean4__Q3527102), "Kruskal–Katona theorem": among
-- uniform finite set families, a colex initial segment of no greater cardinality
-- has shadow no larger than that of the compared family. This file contains no proof.

module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Mathlib.Data.Finset.Fin

@[expose] public section

open Nat
open scoped FinsetFamily

namespace Finset
namespace Q3527102

open Colex

variable {r n : ℕ} {𝒜 𝒞 : Finset <| Finset <| Fin n}

/-- The Kruskal–Katona shadow bound for an initial segment of the colex order. -/
theorem kruskal_katona_statement
    (h𝒜r : (𝒜 : Set (Finset (Fin n))).Sized r) (h𝒞𝒜 : #𝒞 ≤ #𝒜)
    (h𝒞 : IsInitSeg 𝒞 r) : #(∂ 𝒞) ≤ #(∂ 𝒜) := sorry

end Q3527102
end Finset
