import Mathlib

open Topology Filter Set Polynomial Function

abbrev putnam_1981_b1_solution : ℝ := -1
/--
Find the value of $$\lim_{n \rightarrow \infty} \frac{1}{n^5}\sum_{h=1}^{n}\sum_{k=1}^{n}(5h^4 - 18h^2k^2 + 5k^4).$$
-/
theorem putnam_1981_b1
(f : ℕ → ℝ)
(hf : f = fun n : ℕ => ((1 : ℝ)/n^5) * ∑ h ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, (5*(h : ℝ)^4 - 18*h^2*k^2 + 5*k^4))
: Tendsto f atTop (𝓝 putnam_1981_b1_solution) :=
sorry
