-- Statement-only formalization of Thousand Theorems artifact Q576478
-- (thousand-theorems__lean4__Q576478), "Liouville's theorem (complex analysis)":
-- a globally complex-differentiable map between complex normed spaces with bounded range
-- takes equal values at every pair of points. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

universe u v

-- Restore the canonical complex normed-field instances omitted by the reduced module graph.
noncomputable local instance : NormedField ℂ where
  dist_eq _ _ := rfl
  norm_mul := Complex.norm_mul

noncomputable local instance : NontriviallyNormedField ℂ where
  non_trivial := ⟨2, Complex.norm_two.symm ▸ one_lt_two⟩

namespace Q576478

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Liouville's theorem for bounded complex-differentiable maps between complex normed spaces. -/
theorem apply_eq_apply_of_bounded_statement {f : E → F} (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) (z w : E) : f z = f w := sorry

end Q576478
