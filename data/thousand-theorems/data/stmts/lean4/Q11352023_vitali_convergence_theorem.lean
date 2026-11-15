-- Statement-only formalization of Thousand Theorems artifact Q11352023
-- (thousand-theorems__lean4__Q11352023), "Vitali convergence theorem": convergence
-- in measure together with uniform integrability and uniform tightness is equivalent
-- to convergence in Lp. This file contains no proof.

module

public import Mathlib.MeasureTheory.Function.UnifTight

@[expose] public section

namespace MeasureTheory

open Set Filter Topology NNReal ENNReal

namespace Q11352023

variable {α β : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]

/-- Vitali's convergence theorem on a measure space of not necessarily finite measure. -/
theorem tendstoInMeasure_iff_tendsto_Lp {p : ℝ≥0∞} {f : ℕ → α → β} {g : α → β}
    (hp : 1 ≤ p) (hp' : p ≠ ⊤) (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) :
    TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) := sorry

end Q11352023

end MeasureTheory
