import Mathlib

open Topology Filter Set Polynomial Function

noncomputable abbrev putnam_1981_a1_solution : ℝ := 1 / 8
/--
Let $E(n)$ be the greatest integer $k$ such that $5^k$ divides $1^1 2^2 3^3 \cdots n^n$. Find $\lim_{n \rightarrow \infty} \frac{E(n)}{n^2}$.
-/
theorem putnam_1981_a1
    (P : ℕ → ℕ → Prop)
    (hP : ∀ n k, P n k ↔ 5^k ∣ ∏ m ∈ Finset.Icc 1 n, (m^m : ℤ))
    (E : ℕ → ℕ)
    (hE : ∀ n ∈ Ici 1, P n (E n) ∧ ∀ k : ℕ, P n k → k ≤ E n) :
    Tendsto (fun n : ℕ => ((E n) : ℝ)/n^2) atTop (𝓝 putnam_1981_a1_solution) :=
  sorry
