-- Statement-only formalization of Thousand Theorems artifact Q1472120
-- (thousand-theorems__lean4__Q1472120), "Hellinger–Toeplitz theorem": a symmetric
-- linear operator on a complete real or complex inner product space is continuous.
-- This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

def IsSymmetric (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, inner 𝕜 (T x) y = inner 𝕜 x (T y)

/-- The Hellinger–Toeplitz theorem for symmetric linear operators. -/
theorem IsSymmetric.continuous [CompleteSpace E] {T : E →ₗ[𝕜] E}
    (hT : IsSymmetric T) : Continuous T := sorry

end LinearMap
