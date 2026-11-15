/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

/-!
# Quadratic reciprocity.

## Main results

We prove the law of quadratic reciprocity, see `legendreSym.quadratic_reciprocity` and
`legendreSym.quadratic_reciprocity'`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` and
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

We also prove the supplementary laws that give conditions for when `2` or `-2`
is a square modulo a prime `p`:
`legendreSym.at_two` and `ZMod.exists_sq_eq_two_iff` for `2` and
`legendreSym.at_neg_two` and `ZMod.exists_sq_eq_neg_two_iff` for `-2`.

## Implementation notes

The proofs use results for quadratic characters on arbitrary finite fields
from `NumberTheory.LegendreSymbol.QuadraticChar.GaussSum`, which in turn are based on
properties of quadratic Gauss sums as provided by `NumberTheory.LegendreSymbol.GaussSum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/

public section


open Nat

section Values

variable {p : ℕ} [Fact p.Prime]

open ZMod

/-!
### The value of the Legendre symbol at `2` and `-2`

See `jacobiSym.at_two` and `jacobiSym.at_neg_two` for the corresponding statements
for the Jacobi symbol.
-/


namespace legendreSym

/-- `legendreSym p 2` is given by `χ₈ p`. -/
theorem at_two (hp : p ≠ 2) : legendreSym p 2 = χ₈ p := by sorry
theorem at_neg_two (hp : p ≠ 2) : legendreSym p (-2) = χ₈' p := by sorry
end legendreSym

namespace ZMod

/-- `2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `8`. -/
theorem exists_sq_eq_two_iff (hp : p ≠ 2) : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 := by sorry
theorem exists_sq_eq_neg_two_iff (hp : p ≠ 2) : IsSquare (-2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 3 := by sorry
end ZMod

end Values

section Reciprocity

/-!
### The Law of Quadratic Reciprocity

See `jacobiSym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
for the Jacobi symbol.
-/


variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

namespace legendreSym

open ZMod

/-- **The Law of Quadratic Reciprocity**: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) := by sorry
theorem quadratic_reciprocity' (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q := by sorry
theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q := by sorry
theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q := by sorry
end legendreSym

namespace ZMod

open legendreSym

/-- If `p` and `q` are odd primes and `p % 4 = 1`, then `q` is a square mod `p` iff
`p` is a square mod `q`. -/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
    IsSquare (q : ZMod p) ↔ IsSquare (p : ZMod q) := by sorry
theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    (hpq : p ≠ q) : IsSquare (q : ZMod p) ↔ ¬IsSquare (p : ZMod q) := by sorry
end ZMod

end Reciprocity
