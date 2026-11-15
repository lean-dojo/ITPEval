-- Statement-only formalization of Thousand Theorems artifact Q476776
-- (thousand-theorems__lean4__Q476776), "Solutions of a general quartic equation":
-- over a field with invertible 2, Ferrari's auxiliary quantities, including a root
-- of the cubic resolvent, characterize the roots of a quartic when `q` is nonzero.
-- This file contains no proof.

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.Invertible

@[expose] public section

namespace Theorems100

variable {K : Type*} [Field K] (a b c d e : K) {p q r s u v w : K}
variable [Invertible (2 : K)]

/-- The roots of a quartic polynomial when the Ferrari parameter `q` is nonzero. -/
theorem quartic_eq_zero_iff (ha : a ≠ 0)
    (hp : p = (8 * a * c - 3 * b ^ 2) / (8 * a ^ 2))
    (hq : q = (b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d) / (8 * a ^ 3))
    (hq_nonzero : q ≠ 0)
    (hr : r =
      (16 * a * b ^ 2 * c + 256 * a ^ 3 * e - 3 * b ^ 4 - 64 * a ^ 2 * b * d) /
        (256 * a ^ 4))
    (hu : u ^ 3 - p * u ^ 2 - 4 * r * u + 4 * p * r - q ^ 2 = 0)
    (hs : s ^ 2 = u - p)
    (hv : v ^ 2 = 4 * s ^ 2 - 8 * (u - q / s))
    (hw : w ^ 2 = 4 * s ^ 2 - 8 * (u + q / s)) (x : K) :
    a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0 ↔
      x = (-2 * s - v) / 4 - b / (4 * a) ∨
        x = (-2 * s + v) / 4 - b / (4 * a) ∨
          x = (2 * s - w) / 4 - b / (4 * a) ∨
            x = (2 * s + w) / 4 - b / (4 * a) := sorry

end Theorems100
