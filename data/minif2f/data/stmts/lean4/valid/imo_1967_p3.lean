-- Statement-only formalization of miniF2F valid problem imo_1967_p3. This file
-- contains no proof.

import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1967_p3 (k m n : ℕ) (c : ℕ → ℕ) (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : ∀ s, c s = s * (s + 1)) (h₂ : Nat.Prime (k + m + 1)) (h₃ : n + 1 < k + m + 1) :
  (∏ i ∈ Finset.Icc 1 n, (c i : ℤ)) ∣
    ∏ i ∈ Finset.Icc 1 n, ((c (m + i) : ℤ) - (c k : ℤ)) := by sorry
