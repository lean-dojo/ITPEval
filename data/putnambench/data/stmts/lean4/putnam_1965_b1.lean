import Mathlib

open EuclideanGeometry Topology Filter Complex

noncomputable abbrev putnam_1965_b1_solution : ℝ := 1 / 2
/--
Find $$\lim_{n \to \infty} \int_{0}^{1} \int_{0}^{1} \cdots \int_{0}^{1} \cos^2\left(\frac{\pi}{2n}(x_1 + x_2 + \cdots + x_n)\right) dx_1 dx_2 \cdots dx_n.$$
-/
theorem putnam_1965_b1
: Tendsto (fun n : ℕ ↦ ∫ x in {x : Fin (n+1) → ℝ | ∀ k : Fin (n+1), x k ∈ Set.Icc 0 1}, (Real.cos (Real.pi/(2 * (n+1)) * ∑ k : Fin (n+1), x k))^2) atTop (𝓝 putnam_1965_b1_solution) :=
sorry
