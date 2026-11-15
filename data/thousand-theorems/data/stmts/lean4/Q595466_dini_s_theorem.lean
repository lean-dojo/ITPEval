-- Statement-only formalization of Thousand Theorems artifact Q595466
-- (thousand-theorems__lean4__Q595466), "Dini's theorem": a monotone family of
-- continuous functions that converges pointwise to a continuous limit converges
-- locally uniformly. This file contains no proof.

module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.UniformSpace.CompactConvergence

@[expose] public section

open Filter Topology

namespace Q595466

variable {ι α G : Type*} [Preorder ι] [TopologicalSpace α]
  [NormedAddCommGroup G] [Lattice G] [HasSolidNorm G] [IsOrderedAddMonoid G]

namespace Monotone

/-- Dini's theorem for locally uniform convergence of a monotone family. -/
theorem tendstoLocallyUniformly_of_forall_tendsto {F : ι → α → G} {f : α → G}
    (hF_cont : ∀ i, Continuous (F i)) (hF_mono : Monotone F) (hf : Continuous f)
    (h_tendsto : ∀ x, Tendsto (F · x) atTop (𝓝 (f x))) :
    TendstoLocallyUniformly F f atTop := sorry

end Monotone

end Q595466
