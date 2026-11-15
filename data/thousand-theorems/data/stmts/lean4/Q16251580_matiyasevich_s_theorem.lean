-- Statement-only formalization of Thousand Theorems artifact Q16251580
-- (thousand-theorems__lean4__Q16251580), "Matiyasevich's theorem": membership
-- in the natural Pell sequence is equivalent to solvability of an explicit
-- system of Pell equations, congruences, and divisibility conditions.
-- This file contains no proof.

module

public import Mathlib.NumberTheory.PellMatiyasevic

@[expose] public section

open Nat

namespace Q16251580

/-- Matiyasevich's characterization of pairs in the natural Pell sequence. -/
theorem matiyasevic {a k x y : ℕ} :
    (∃ a1 : 1 < a, Pell.xn a1 k = x ∧ Pell.yn a1 k = y) ↔
      1 < a ∧ k ≤ y ∧ (x = 1 ∧ y = 0 ∨
        ∃ u v s t b : ℕ,
          x * x - (a * a - 1) * y * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧
          s * s - (b * b - 1) * t * t = 1 ∧ 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧
          b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧
          t ≡ k [MOD 4 * y]) := sorry

end Q16251580
