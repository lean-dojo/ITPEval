import Mathlib

open Set Function Filter Topology Polynomial Real

noncomputable abbrev putnam_1982_b3_solution : ℝ := (4 / 3) * (Real.sqrt 2 - 1)
/--
Let $p_n$ denote the probability that $c + d$ will be a perfect square if $c$ and $d$ are selected independently and uniformly at random from $\{1, 2, 3, \dots, n\}$. Express $\lim_{n \rightarrow \infty} p_n \sqrt{n}$ in the form $r(\sqrt{s} - t)$ for integers $s$ and $t$ and rational $r$.
-/
theorem putnam_1982_b3
(p : ℕ → ℝ)
(hp : p = fun n : ℕ => ({(c, d) : Finset.Icc 1 n × Finset.Icc 1 n | ∃ m : ℕ, m^2 = c + d}.ncard : ℝ) / n^2)
: Tendsto (fun n : ℕ => p n * Real.sqrt n) atTop (𝓝 putnam_1982_b3_solution) :=
sorry
