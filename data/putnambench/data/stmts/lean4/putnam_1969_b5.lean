import Mathlib

open Matrix Filter Topology Set Nat

/--
Let $a_1 < a_2 < a_3 < \dots$ be an increasing sequence of positive integers. Assume that the sequences $\sum_{i = 1}^{\infty} 1/(a n)$ is convergent. For any number $x$, let $k(x)$ be the number of $a_n$'s which do not exceed $x$. Show that $\lim_{x \to \infty} k(x)/x = 0$.
-/
theorem putnam_1969_b5
(a : ℕ → ℕ)
(ha : StrictMono a ∧ ∀ x : ℕ, a x > 0)
(hinvasum : ∃ C : ℝ, Tendsto (fun n => ∑ i : Fin n, 1 / (a i : ℝ)) atTop (𝓝 C))
(k : ℕ → ℕ)
(hk : k = fun x => {n | a n ≤ x}.ncard)
: Tendsto (fun t => (k t : ℝ) / (t : ℝ)) atTop (𝓝 0) :=
sorry
