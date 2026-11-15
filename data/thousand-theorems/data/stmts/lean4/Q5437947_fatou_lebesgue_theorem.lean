-- Statement-only formalization of Thousand Theorems artifact Q5437947
-- (thousand-theorems__lean4__Q5437947), "Fatou–Lebesgue theorem": for a
-- sequence of measurable extended-nonnegative functions, the lower Lebesgue
-- integral of the pointwise limit inferior is at most the limit inferior of
-- their lower Lebesgue integrals. This file contains no proof.

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal MeasureTheory

namespace Q5437947

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Fatou's lemma for a sequence of measurable extended-nonnegative functions. -/
theorem fatou_lebesgue_theorem {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
    ∫⁻ a, liminf (fun n ↦ f n a) atTop ∂μ ≤
      liminf (fun n ↦ ∫⁻ a, f n a ∂μ) atTop := sorry

end Q5437947
