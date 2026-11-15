-- Statement-only formalization of Thousand Theorems artifact Q530152
-- (thousand-theorems__lean4__Q530152), "Picard–Lindelöf theorem": local existence
-- of a solution to a time-dependent ordinary differential equation under the
-- Picard–Lindelöf hypotheses, with a prescribed initial value. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

open Metric Set
open scoped NNReal

namespace Q530152

/-- The hypotheses of the Picard-Lindelöf theorem on a closed time interval and ball. -/
structure IsPicardLindelof {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) {tmin tmax : ℝ} (t₀ : Icc tmin tmax) (x₀ : E)
    (a r L K : ℝ≥0) : Prop where
  lipschitzOnWith : ∀ t ∈ Icc tmin tmax, LipschitzOnWith K (f t) (closedBall x₀ a)
  continuousOn : ∀ x ∈ closedBall x₀ a, ContinuousOn (f · x) (Icc tmin tmax)
  norm_le : ∀ t ∈ Icc tmin tmax, ∀ x ∈ closedBall x₀ a, ‖f t x‖ ≤ L
  mul_max_le : L * max (tmax - t₀) (t₀ - tmin) ≤ a - r

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ x : E} {a r L K : ℝ≥0}

/-- The differential-form Picard-Lindelöf local existence theorem. -/
theorem exists_eq_forall_mem_Icc_hasDerivWithinAt
    (hf : IsPicardLindelof f t₀ x₀ a r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ α : ℝ → E, α t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t := sorry

end Q530152
