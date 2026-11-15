-- Statement-only formalization of Thousand Theorems artifact Q303402
-- (thousand-theorems__lean4__Q303402), "Rank–nullity theorem": for a linear
-- map, the rank of its range plus the rank of its kernel equals the rank of
-- its domain. This file contains no proof.

module

public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section

universe u v

namespace Q303402

variable {R : Type v} {M M₁ : Type u} [Ring R]
variable [AddCommGroup M] [AddCommGroup M₁]
variable [Module R M] [Module R M₁] [HasRankNullity.{u} R]

/-- The rank–nullity theorem for a linear map. -/
theorem rank_nullity_theorem_statement (f : M →ₗ[R] M₁) :
    Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) =
      Module.rank R M := sorry

end Q303402
