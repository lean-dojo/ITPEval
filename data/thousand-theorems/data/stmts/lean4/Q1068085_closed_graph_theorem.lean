-- Statement-only formalization of Thousand Theorems artifact Q1068085
-- (thousand-theorems__lean4__Q1068085), "Closed graph theorem": a linear map
-- between Banach spaces whose graph is closed is continuous. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Baire.CompleteMetrizable

@[expose] public section

variable {𝕜 E F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The closed graph theorem for linear maps between Banach spaces. -/
theorem LinearMap.continuous_of_isClosed_graph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g := sorry
