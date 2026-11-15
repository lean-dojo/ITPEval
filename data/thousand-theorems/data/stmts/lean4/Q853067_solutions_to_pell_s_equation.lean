-- Statement-only formalization of Thousand Theorems artifact Q853067
-- (thousand-theorems__lean4__Q853067), "Solutions to Pell's equation": every
-- natural-number solution of x^2 - (a^2 - 1)y^2 = 1 for a > 1 occurs in the
-- recursively generated Pell sequence. This file contains no proof.

module

public section

namespace Pell

/-- The coefficient `a^2 - 1` in this family of Pell equations. -/
def d {a : Nat} (_a1 : 1 < a) : Nat :=
  a * a - 1

/-- The recursively generated pairs of natural-number Pell solutions. -/
def pell {a : Nat} (a1 : 1 < a) : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
      ((pell a1 n).1 * a + d a1 * (pell a1 n).2,
        (pell a1 n).1 + (pell a1 n).2 * a)

/-- The first coordinate of the Pell sequence. -/
def xn {a : Nat} (a1 : 1 < a) (n : Nat) : Nat :=
  (pell a1 n).1

/-- The second coordinate of the Pell sequence. -/
def yn {a : Nat} (a1 : 1 < a) (n : Nat) : Nat :=
  (pell a1 n).2

/-- Every natural-number solution is a member of the recursively generated Pell sequence. -/
theorem eq_pell {a : Nat} (a1 : 1 < a) {x y : Nat}
    (hp : x * x - d a1 * y * y = 1) :
    ∃ n, x = xn a1 n ∧ y = yn a1 n := sorry

end Pell
