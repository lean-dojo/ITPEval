-- Statement-only formalization of Thousand Theorems artifact Q318767
-- (thousand-theorems__lean4__Q318767), "Abel's theorem": convergence of coefficient
-- partial sums determines the boundary limit of the associated complex power series
-- within positive Stolz cones and of the real power series from the left. This file
-- contains no proof.

module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

open Filter Finset

open scoped Topology

namespace Q318767

namespace Complex

variable {f : ℕ → ℂ} {l : ℂ}

/-- Abel's limit theorem for a complex power series within a positive Stolz cone. -/
theorem tendsto_tsum_powerSeries_nhdsWithin_stolzCone
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l))
    {s : ℝ} (hs : 0 < s) :
    Tendsto (fun z ↦ ∑' n, f n * z ^ n)
      (𝓝[{z : ℂ | |z.im| < s * (1 - z.re)}] 1) (𝓝 l) := sorry

end Complex

namespace Real

variable {f : ℕ → ℝ} {l : ℝ}

/-- Abel's limit theorem for a real power series approaching `1` from the left. -/
theorem tendsto_tsum_powerSeries_nhdsWithin_lt
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] 1) (𝓝 l) := sorry

end Real

end Q318767
