-- Statement-only formalization of Thousand Theorems artifact Q9993851
-- (thousand-theorems__lean4__Q9993851), "Lax-Milgram theorem": a coercive bounded
-- bilinear form on a real Hilbert space upgrades its associated continuous linear map
-- to a continuous linear equivalence. This file contains no proof.

module

import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Operator.NormedSpace

universe u

namespace Q9993851

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- The Lax-Milgram equivalence associated to a coercive bounded bilinear form. -/
theorem lax_milgram_statement (coercive : IsCoercive B) :
    ∃ e : V ≃L[ℝ] V, ∀ v w : V, inner ℝ (e v) w = B v w := sorry

end Q9993851
