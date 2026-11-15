-- Statement-only formalization of Thousand Theorems artifact Q1217677
-- (thousand-theorems__lean4__Q1217677), "Fundamental theorem of calculus":
-- a variable-endpoint interval integral has the expected strict derivative under an
-- almost-everywhere limit, and integrating an integrable right derivative recovers endpoint
-- subtraction. This file contains no proof.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

namespace Q1217677

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f f' : ℝ → E} {c : E} {a b : ℝ}

/-- FTC-1 for a variable right endpoint under an almost-everywhere limit at that endpoint. -/
theorem integral_hasStrictDerivAt_of_tendsto_ae_right
    (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b))
    (hb : Tendsto f (𝓝 b ⊓ ae volume) (𝓝 c)) :
    HasStrictDerivAt (fun u => ∫ x in a..u, f x) c b := sorry

/-- FTC-2 for a continuous function with an integrable right derivative on an ordered interval. -/
theorem integral_eq_sub_of_hasDeriv_right_of_le
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a := sorry

end Q1217677
