-- Statement-only formalization of Thousand Theorems artifact Q718875
-- (thousand-theorems__lean4__Q718875), "Erdős–Ko–Rado theorem": an intersecting
-- family of uniformly r-sized subsets of Fin n, with r at most n / 2, has
-- cardinality at most (n - 1).choose (r - 1). This file contains no proof.

module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Mathlib.Combinatorics.SetFamily.Intersecting
public import Mathlib.Data.Finset.Fin

@[expose] public section

namespace Finset
namespace Q718875

variable {n r : ℕ} {𝒜 : Finset (Finset (Fin n))}

/-- The Erdős–Ko–Rado cardinality bound for a uniform intersecting family. -/
theorem erdos_ko_rado_statement
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (h₂ : (𝒜 : Set (Finset (Fin n))).Sized r) (h₃ : r ≤ n / 2) :
    #𝒜 ≤ (n - 1).choose (r - 1) := sorry

end Q718875
end Finset
