-- Statement-only formalization of Thousand Theorems artifact Q1346677
-- (thousand-theorems__lean4__Q1346677), "Tietze extension theorem": a bounded
-- continuous real-valued function along a closed embedding into a normal space extends
-- to a bounded continuous function of exactly the same norm. This file contains no proof.

module

public import Mathlib.Topology.TietzeExtension

@[expose] public section

open BoundedContinuousFunction Topology

namespace Q1346677

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]

/-- The norm-preserving Tietze extension theorem for a closed embedding. -/
theorem tietze_extension_theorem_statement (f : X →ᵇ ℝ) {e : X → Y}
    (he : IsClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g ∘ e = f := sorry

end Q1346677
