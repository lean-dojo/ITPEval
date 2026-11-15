-- Statement-only formalization of PutnamBench artifact putnam_1996_a1:
-- the minimum rectangle area satisfying the specified packing inequalities for every
-- pair of positive side lengths whose squared lengths sum to one. This file contains no proof.

import Mathlib.Data.Real.Sqrt

noncomputable def putnam_1996_a1_solution : ℝ := (1 + Real.sqrt 2) / 2

theorem putnam_1996_a1 :
    let packable : ℝ → ℝ → ℝ → ℝ → Prop :=
      fun n1 n2 a1 a2 ↦
        n1 + n2 ≤ max a1 a2 ∧ max n1 n2 ≤ min a1 a2
    let Aprop : ℝ → Prop :=
      fun A ↦
        ∀ n1 n2 : ℝ,
          0 < n1 ∧ 0 < n2 ∧ n1 ^ 2 + n2 ^ 2 = 1 →
            ∃ a1 a2 : ℝ,
              0 < a1 ∧ 0 < a2 ∧ a1 * a2 = A ∧ packable n1 n2 a1 a2
    Aprop putnam_1996_a1_solution ∧
      ∀ A : ℝ, Aprop A → A ≥ putnam_1996_a1_solution :=
  sorry
