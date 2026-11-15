-- Statement-only formalization of Thousand Theorems artifact Q660799
-- (thousand-theorems__lean4__Q660799), "Darboux's theorem (analysis)":
-- derivatives on real intervals take intermediate values, so their images of
-- order-connected or convex sets remain order-connected or convex. This file contains no proof.

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

public section

open Filter Set

open scoped Topology

namespace Q660799

variable {a b : ℝ} {f f' : ℝ → ℝ}

/-- Darboux's theorem for a derivative increasing strictly across two endpoint values. -/
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt_statement (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ}
    (hma : f' a < m) (hmb : m < f' b) : m ∈ f' '' Ioo a b := sorry

/-- Darboux's theorem for a derivative decreasing strictly across two endpoint values. -/
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt_statement (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ}
    (hma : m < f' a) (hmb : f' b < m) : m ∈ f' '' Ioo a b := sorry

/-- The derivative-value image of an order-connected set is order-connected. -/
theorem ordConnected_image_hasDerivWithinAt_statement {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : OrdConnected (f' '' s) := sorry

/-- The `derivWithin` image of an order-connected set is order-connected. -/
theorem ordConnected_image_derivWithin_statement {s : Set ℝ} (hs : OrdConnected s)
    (hf : DifferentiableOn ℝ f s) : OrdConnected (derivWithin f s '' s) := sorry

/-- The derivative image of an order-connected set is order-connected. -/
theorem ordConnected_image_deriv_statement {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : OrdConnected (deriv f '' s) := sorry

/-- The derivative-value image of a convex real set is convex. -/
theorem convex_image_hasDerivWithinAt_statement {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) : Convex ℝ (f' '' s) := sorry

/-- The `derivWithin` image of a convex real set is convex. -/
theorem convex_image_derivWithin_statement {s : Set ℝ} (hs : Convex ℝ s)
    (hf : DifferentiableOn ℝ f s) : Convex ℝ (derivWithin f s '' s) := sorry

/-- The derivative image of a convex real set is convex. -/
theorem convex_image_deriv_statement {s : Set ℝ} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : Convex ℝ (deriv f '' s) := sorry

/-- Darboux's theorem on a closed interval between nondecreasing endpoint values. -/
theorem exists_hasDerivWithinAt_eq_of_ge_of_le_statement (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ}
    (hma : f' a ≤ m) (hmb : m ≤ f' b) : m ∈ f' '' Icc a b := sorry

/-- The second indexed closed-interval statement, with its source endpoint inequalities. -/
theorem exists_hasDerivWithinAt_eq_of_le_of_ge_statement (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ}
    (hma : f' a ≤ m) (hmb : m ≤ f' b) : m ∈ f' '' Icc a b := sorry

end Q660799
