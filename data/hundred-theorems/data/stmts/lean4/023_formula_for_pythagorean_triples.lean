/-
Copyright (c) 2020 Paul van Wamelen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul van Wamelen
-/
module

public import Mathlib.Data.Int.NatPrime
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Field

/-!
# Pythagorean Triples

The main result is the classification of Pythagorean triples. The final result is for general
Pythagorean triples. It follows from the more interesting relatively prime case. We use the
"rational parametrization of the circle" method for the proof. The parametrization maps the point
`(x / z, y / z)` to the slope of the line through `(-1, 0)` and `(x / z, y / z)`. This quickly
shows that `(x / z, y / z) = (2 * m * n / (m ^ 2 + n ^ 2), (m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2))` where
`m / n` is the slope. In order to identify numerators and denominators we now need results showing
that these are coprime. This is easy except for the prime 2. In order to deal with that we have to
analyze the parity of `x`, `y`, `m` and `n` and eliminate all the impossible cases. This takes up
the bulk of the proof below.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

theorem sq_ne_two_fin_zmod_four (z : ZMod 4) : z * z ≠ 2 := by sorry
theorem Int.sq_ne_two_mod_four (z : ℤ) : z * z % 4 ≠ 2 := by sorry
def PythagoreanTriple (x y z : ℤ) : Prop :=
  x * x + y * y = z * z

/-- Pythagorean triples are interchangeable, i.e `x * x + y * y = y * y + x * x = z * z`.
This comes from additive commutativity. -/
theorem pythagoreanTriple_comm {x y z : ℤ} : PythagoreanTriple x y z ↔ PythagoreanTriple y x z := by sorry
theorem PythagoreanTriple.zero : PythagoreanTriple 0 0 0 := by sorry
namespace PythagoreanTriple

variable {x y z : ℤ}

theorem eq (h : PythagoreanTriple x y z) : x * x + y * y = z * z :=
  h

@[symm]
theorem symm (h : PythagoreanTriple x y z) : PythagoreanTriple y x z := by sorry
theorem mul (h : PythagoreanTriple x y z) (k : ℤ) : PythagoreanTriple (k * x) (k * y) (k * z) :=
  calc
    k * x * (k * x) + k * y * (k * y) = k ^ 2 * (x * x + y * y) := by ring
    _ = k ^ 2 * (z * z) := by rw [h.eq]
    _ = k * z * (k * z) := by ring

/-- `(k*x, k*y, k*z)` is a Pythagorean triple if and only if
`(x, y, z)` is also a triple. -/
theorem mul_iff (k : ℤ) (hk : k ≠ 0) :
    PythagoreanTriple (k * x) (k * y) (k * z) ↔ PythagoreanTriple x y z := by sorry
def IsClassified (_ : PythagoreanTriple x y z) :=
  ∃ k m n : ℤ,
    (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
        x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
      Int.gcd m n = 1

/-- A primitive Pythagorean triple `x, y, z` is a Pythagorean triple with `x` and `y` coprime.
Such a triple is “primitively classified” if there exist coprime integers `m, n` such that either
* `x = m ^ 2 - n ^ 2` and `y = 2 * m * n`, or
* `x = 2 * m * n` and `y = m ^ 2 - n ^ 2`.
-/
@[nolint unusedArguments]
def IsPrimitiveClassified (_ : PythagoreanTriple x y z) :=
  ∃ m n : ℤ,
    (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
      Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0)

variable (h : PythagoreanTriple x y z)
include h

theorem mul_isClassified (k : ℤ) (hc : h.IsClassified) : (h.mul k).IsClassified := by sorry
theorem even_odd_of_coprime (hc : Int.gcd x y = 1) :
    x % 2 = 0 ∧ y % 2 = 1 ∨ x % 2 = 1 ∧ y % 2 = 0 := by sorry
theorem gcd_dvd : (Int.gcd x y : ℤ) ∣ z := by sorry
theorem normalize : PythagoreanTriple (x / Int.gcd x y) (y / Int.gcd x y) (z / Int.gcd x y) := by sorry
theorem isClassified_of_isPrimitiveClassified (hp : h.IsPrimitiveClassified) : h.IsClassified := by sorry
theorem isClassified_of_normalize_isPrimitiveClassified (hc : h.normalize.IsPrimitiveClassified) :
    h.IsClassified := by sorry
theorem ne_zero_of_coprime (hc : Int.gcd x y = 1) : z ≠ 0 := by sorry
theorem isPrimitiveClassified_of_coprime_of_zero_left (hc : Int.gcd x y = 1) (hx : x = 0) :
    h.IsPrimitiveClassified := by sorry
theorem coprime_of_coprime (hc : Int.gcd x y = 1) : Int.gcd y z = 1 := by sorry
end PythagoreanTriple

section circleEquivGen

/-!
### A parametrization of the unit circle

For the classification of Pythagorean triples, we will use a parametrization of the unit circle.
-/


variable {K : Type*} [Field K]

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- A parameterization of the unit circle that is useful for classifying Pythagorean triples.
(To be applied in the case where `K = ℚ`.) -/
def circleEquivGen (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) :
    K ≃ { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 } where
  toFun x :=
    ⟨⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩, by field [hk x], by
      simp only [Ne, div_eq_iff (hk x), neg_mul, one_mul, neg_add, sub_eq_add_neg, add_left_inj]
      simpa only [eq_neg_iff_add_eq_zero, one_pow] using hk 1⟩
  invFun p := (p : K × K).1 / ((p : K × K).2 + 1)
  left_inv x := by sorry
theorem circleEquivGen_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0) (x : K) :
    (circleEquivGen hk x : K × K) = ⟨2 * x / (1 + x ^ 2), (1 - x ^ 2) / (1 + x ^ 2)⟩ :=
  rfl

@[simp]
theorem circleEquivGen_symm_apply (hk : ∀ x : K, 1 + x ^ 2 ≠ 0)
    (v : { p : K × K // p.1 ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≠ -1 }) :
    (circleEquivGen hk).symm v = (v : K × K).1 / ((v : K × K).2 + 1) :=
  rfl

end circleEquivGen

private theorem coprime_sq_sub_sq_add_of_even_odd {m n : ℤ} (h : Int.gcd m n = 1) (hm : m % 2 = 0)
    (hn : n % 2 = 1) : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1 := by sorry
namespace PythagoreanTriple

variable {x y z : ℤ} (h : PythagoreanTriple x y z)

theorem isPrimitiveClassified_aux (hc : x.gcd y = 1) (hzpos : 0 < z) {m n : ℤ}
    (hm2n2 : 0 < m ^ 2 + n ^ 2) (hv2 : (x : ℚ) / z = 2 * m * n / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (hw2 : (y : ℚ) / z = ((m : ℚ) ^ 2 - (n : ℚ) ^ 2) / ((m : ℚ) ^ 2 + (n : ℚ) ^ 2))
    (H : Int.gcd (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) = 1) (co : Int.gcd m n = 1)
    (pp : m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) : h.IsPrimitiveClassified := by sorry
theorem isPrimitiveClassified_of_coprime_of_odd_of_pos (hc : Int.gcd x y = 1) (hyo : y % 2 = 1)
    (hzpos : 0 < z) : h.IsPrimitiveClassified := by sorry
theorem isPrimitiveClassified_of_coprime_of_pos (hc : Int.gcd x y = 1) (hzpos : 0 < z) :
    h.IsPrimitiveClassified := by sorry
theorem isPrimitiveClassified_of_coprime (hc : Int.gcd x y = 1) : h.IsPrimitiveClassified := by sorry
theorem classified : h.IsClassified := by sorry
theorem coprime_classification :
    PythagoreanTriple x y z ∧ Int.gcd x y = 1 ↔
      ∃ m n,
        (x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∨ x = 2 * m * n ∧ y = m ^ 2 - n ^ 2) ∧
          (z = m ^ 2 + n ^ 2 ∨ z = -(m ^ 2 + n ^ 2)) ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) := by sorry
theorem coprime_classification' {x y z : ℤ} (h : PythagoreanTriple x y z)
    (h_coprime : Int.gcd x y = 1) (h_parity : x % 2 = 1) (h_pos : 0 < z) :
    ∃ m n,
      x = m ^ 2 - n ^ 2 ∧
        y = 2 * m * n ∧
          z = m ^ 2 + n ^ 2 ∧
            Int.gcd m n = 1 ∧ (m % 2 = 0 ∧ n % 2 = 1 ∨ m % 2 = 1 ∧ n % 2 = 0) ∧ 0 ≤ m := by sorry
theorem classification :
    PythagoreanTriple x y z ↔
      ∃ k m n,
        (x = k * (m ^ 2 - n ^ 2) ∧ y = k * (2 * m * n) ∨
            x = k * (2 * m * n) ∧ y = k * (m ^ 2 - n ^ 2)) ∧
          (z = k * (m ^ 2 + n ^ 2) ∨ z = -k * (m ^ 2 + n ^ 2)) := by sorry
end PythagoreanTriple
