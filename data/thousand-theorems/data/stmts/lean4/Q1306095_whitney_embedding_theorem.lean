-- Statement-only formalization of Thousand Theorems artifact Q1306095
-- (thousand-theorems__lean4__Q1306095), "Whitney embedding theorem": every compact Hausdorff
-- smooth finite-dimensional real manifold admits a smooth closed embedding into some
-- finite-dimensional Euclidean space with injective manifold derivative everywhere.
-- This file contains no proof.

import Mathlib

universe uE uH uM

open Function Topology
open scoped Manifold ContDiff

namespace Q1306095

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- Every compact Hausdorff smooth real manifold embeds smoothly into some Euclidean space. -/
theorem exists_embedding_euclidean_of_compact [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      CMDiff ∞ e ∧ IsClosedEmbedding e ∧ ∀ x : M, Injective (mfderiv% e x) := sorry

end Q1306095
