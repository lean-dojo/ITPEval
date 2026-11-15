-- Statement-only formalization of Thousand Theorems artifact Q1357684
-- (thousand-theorems__lean4__Q1357684), "Riesz representation theorem": a Hilbert
-- space over the real or complex numbers is conjugate-linearly isometrically equivalent
-- to its strong dual via the inner product. This file contains no proof.

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

noncomputable section

namespace Q1357684

open InnerProductSpace RCLike

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The Fréchet-Riesz representation as the canonical isometric equivalence with the dual. -/
theorem riesz_representation_theorem :
    ∃ e : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E, ∀ x y : E, e x y = inner 𝕜 x y := sorry

end Q1357684
