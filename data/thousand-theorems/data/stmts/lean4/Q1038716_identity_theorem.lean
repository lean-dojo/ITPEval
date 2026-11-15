-- Statement-only formalization of Thousand Theorems artifact Q1038716
-- (thousand-theorems__lean4__Q1038716), "Identity theorem": two functions analytic on
-- neighborhoods of a preconnected set agree on the whole set if they agree frequently in a
-- punctured neighborhood of a point of the set. This file contains no proof.

module

public import Mathlib.Analysis.Analytic.Uniqueness

@[expose] public section

open Filter Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f g : 𝕜 → E} {z₀ : 𝕜}

namespace AnalyticOnNhd

variable {U : Set 𝕜}

/-- The identity theorem for analytic functions on a preconnected set. -/
theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (h₀ : z₀ ∈ U)
    (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := sorry

end AnalyticOnNhd
