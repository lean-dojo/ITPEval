-- Statement-only formalization of Thousand Theorems artifact Q422187
-- (thousand-theorems__lean4__Q422187), "Myhill–Nerode theorem": a language
-- over an arbitrary alphabet is regular if and only if the set of its left
-- quotients is finite. This file contains no proof.

module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

universe u

namespace Language
namespace Q422187

variable {α : Type u}

/-- The left quotient of `L` by `x` consists of suffixes `y` with `x ++ y ∈ L`. -/
def leftQuotient (L : Language α) (x : List α) : Language α := { y | x ++ y ∈ L }

/-- The Myhill–Nerode characterization of regular languages by left quotients. -/
theorem myhill_nerode_statement (L : Language α) :
    L.IsRegular ↔ (Set.range (leftQuotient L)).Finite := sorry

end Q422187
end Language
