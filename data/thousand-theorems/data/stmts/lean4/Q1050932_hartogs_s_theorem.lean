-- Statement-only formalization of Thousand Theorems artifact Q1050932
-- (thousand-theorems__lean4__Q1050932), "Hartogs's theorem": a function from
-- `ℂ × ℂ` to a separable complex Banach space that is analytic in each coordinate
-- separately at every point of an open set is jointly analytic there. This file contains no proof.

module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-- Hartogs's theorem on `ℂ × ℂ`: separately analytic functions are jointly analytic. -/
theorem Pair.hartogs {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)} (so : IsOpen s)
    (fa0 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, c1)) c0)
    (fa1 : ∀ c0 c1, (c0, c1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (c0, z1)) c1) :
    AnalyticOnNhd ℂ f s := sorry
