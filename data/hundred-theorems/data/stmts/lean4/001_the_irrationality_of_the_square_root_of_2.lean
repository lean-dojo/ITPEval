/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Rat.Sqrt
public import Mathlib.Data.Real.Sqrt
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Irrational real numbers

In this file we define a predicate `Irrational` on `ℝ`, prove that the `n`-th root of an integer
number is irrational if it is not integer, and that `√(q : ℚ)` is irrational if and only if
`¬IsSquare q ∧ 0 ≤ q`.

We also provide dot-style constructors like `Irrational.add_ratCast`, `Irrational.ratCast_sub` etc.

With the `Decidable` instances in this file, is possible to prove `Irrational √n` using `decide`,
when `n` is a numeric literal or cast;
but this only works if you `unseal Nat.sqrt.iter in` before the theorem where you use this proof.
-/

@[expose] public section


open Rat Real

/-- A real number is irrational if it is not equal to any rational number. -/
def Irrational (x : ℝ) :=
  x ∉ Set.range ((↑) : ℚ → ℝ)

theorem irrational_iff_ne_rational (x : ℝ) : Irrational x ↔ ∀ a b : ℤ, b ≠ 0 → x ≠ a / b := by sorry
theorem Irrational.ne_rational {x : ℝ} (hx : Irrational x) (a b : ℤ) : x ≠ a / b := by sorry
theorem exists_rat_of_not_irrational {x : ℝ} (hx : ¬ Irrational x) : ∃ (q : ℚ), x = q := by sorry
theorem Transcendental.irrational {r : ℝ} (tr : Transcendental ℚ r) : Irrational r := by sorry
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m)
    (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x := by sorry
theorem irrational_nrt_of_n_not_dvd_multiplicity {x : ℝ} (n : ℕ) {m : ℤ} (hm : m ≠ 0) (p : ℕ)
    [hp : Fact p.Prime] (hxr : x ^ n = m)
    (hv : multiplicity (p : ℤ) m % n ≠ 0) :
    Irrational x := by sorry
theorem irrational_sqrt_of_multiplicity_odd (m : ℤ) (hm : 0 < m) (p : ℕ) [hp : Fact p.Prime]
    (Hpv : multiplicity (p : ℤ) m % 2 = 1) :
    Irrational (√m) :=
  @irrational_nrt_of_n_not_dvd_multiplicity _ 2 _ (Ne.symm (ne_of_lt hm)) p hp
    (sq_sqrt (Int.cast_nonneg hm.le)) (by rw [Hpv]; exact one_ne_zero)

@[simp] theorem not_irrational_zero : ¬Irrational 0 := not_not_intro ⟨0, Rat.cast_zero⟩
@[simp] theorem not_irrational_one : ¬Irrational 1 := not_not_intro ⟨1, Rat.cast_one⟩

theorem irrational_sqrt_ratCast_iff_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    Irrational (√q) ↔ ¬IsSquare q := by sorry
theorem irrational_sqrt_ratCast_iff {q : ℚ} :
    Irrational (√q) ↔ ¬IsSquare q ∧ 0 ≤ q := by sorry
theorem irrational_sqrt_intCast_iff_of_nonneg {z : ℤ} (hz : 0 ≤ z) :
    Irrational (√z) ↔ ¬IsSquare z := by sorry
theorem irrational_sqrt_intCast_iff {z : ℤ} :
    Irrational (√z) ↔ ¬IsSquare z ∧ 0 ≤ z := by sorry
theorem irrational_sqrt_natCast_iff {n : ℕ} : Irrational (√n) ↔ ¬IsSquare n := by sorry
theorem irrational_sqrt_ofNat_iff {n : ℕ} [n.AtLeastTwo] :
    Irrational √(ofNat(n)) ↔ ¬IsSquare ofNat(n) :=
  irrational_sqrt_natCast_iff

theorem Nat.Prime.irrational_sqrt {p : ℕ} (hp : Nat.Prime p) : Irrational (√p) :=
  irrational_sqrt_natCast_iff.mpr hp.not_isSquare

/-- **Irrationality of the Square Root of 2** -/
theorem irrational_sqrt_two : Irrational (√2) := by sorry
instance {n : ℕ} [n.AtLeastTwo] : Decidable (Irrational √(ofNat(n))) :=
  decidable_of_iff' _ irrational_sqrt_ofNat_iff

instance (n : ℕ) : Decidable (Irrational (√n)) :=
  decidable_of_iff' _ irrational_sqrt_natCast_iff

instance (z : ℤ) : Decidable (Irrational (√z)) :=
  decidable_of_iff' _ irrational_sqrt_intCast_iff

instance (q : ℚ) : Decidable (Irrational (√q)) :=
  decidable_of_iff' _ irrational_sqrt_ratCast_iff

/-!
### Dot-style operations on `Irrational`

#### Coercion of a rational/integer/natural number is not irrational
-/


namespace Irrational

variable {x : ℝ}

/-!
#### Irrational number is not equal to a rational/integer/natural number
-/


theorem ne_rat (h : Irrational x) (q : ℚ) : x ≠ q := fun hq => h ⟨q, hq.symm⟩

theorem ne_int (h : Irrational x) (m : ℤ) : x ≠ m := by sorry
theorem ne_nat (h : Irrational x) (m : ℕ) : x ≠ m :=
  h.ne_int m

theorem ne_zero (h : Irrational x) : x ≠ 0 := mod_cast h.ne_nat 0

theorem ne_one (h : Irrational x) : x ≠ 1 := by simpa only [Nat.cast_one] using h.ne_nat 1

@[simp] theorem ne_ofNat (h : Irrational x) (n : ℕ) [n.AtLeastTwo] : x ≠ ofNat(n) :=
  h.ne_nat n

end Irrational

@[simp]
theorem Rat.not_irrational (q : ℚ) : ¬Irrational q := fun h => h ⟨q, rfl⟩

@[simp]
theorem Int.not_irrational (m : ℤ) : ¬Irrational m := fun h => h.ne_int m rfl

@[simp]
theorem Nat.not_irrational (m : ℕ) : ¬Irrational m := fun h => h.ne_nat m rfl

@[simp] theorem not_irrational_ofNat (n : ℕ) [n.AtLeastTwo] : ¬Irrational ofNat(n) :=
  n.not_irrational
namespace Irrational

variable (q : ℚ) {x y : ℝ}

/-!
#### Addition of rational/integer/natural numbers
-/


/-- If `x + y` is irrational, then at least one of `x` and `y` is irrational. -/
theorem add_cases : Irrational (x + y) → Irrational x ∨ Irrational y := by sorry
theorem of_ratCast_add (h : Irrational (q + x)) : Irrational x :=
  h.add_cases.resolve_left q.not_irrational
theorem ratCast_add (h : Irrational x) : Irrational (q + x) :=
  of_ratCast_add (-q) <| by rwa [cast_neg, neg_add_cancel_left]
theorem of_add_ratCast : Irrational (x + q) → Irrational x :=
  add_comm (↑q) x ▸ of_ratCast_add q
theorem add_ratCast (h : Irrational x) : Irrational (x + q) :=
  add_comm (↑q) x ▸ h.ratCast_add q
theorem of_intCast_add (m : ℤ) (h : Irrational (m + x)) : Irrational x := by sorry
theorem of_add_intCast (m : ℤ) (h : Irrational (x + m)) : Irrational x :=
  of_intCast_add m <| add_comm x m ▸ h
theorem intCast_add (h : Irrational x) (m : ℤ) : Irrational (m + x) := by sorry
theorem add_intCast (h : Irrational x) (m : ℤ) : Irrational (x + m) :=
  add_comm (↑m) x ▸ h.intCast_add m
theorem of_natCast_add (m : ℕ) (h : Irrational (m + x)) : Irrational x :=
  h.of_intCast_add m
theorem of_add_natCast (m : ℕ) (h : Irrational (x + m)) : Irrational x :=
  h.of_add_intCast m
theorem natCast_add (h : Irrational x) (m : ℕ) : Irrational (m + x) :=
  h.intCast_add m
theorem add_natCast (h : Irrational x) (m : ℕ) : Irrational (x + m) :=
  h.add_intCast m
/-!
#### Negation
-/


theorem of_neg (h : Irrational (-x)) : Irrational x := fun ⟨q, hx⟩ => h ⟨-q, by rw [cast_neg, hx]⟩

protected theorem neg (h : Irrational x) : Irrational (-x) :=
  of_neg <| by rwa [neg_neg]

/-!
#### Subtraction of rational/integer/natural numbers
-/


theorem sub_ratCast (h : Irrational x) : Irrational (x - q) := by sorry
theorem ratCast_sub (h : Irrational x) : Irrational (q - x) := by sorry
theorem of_sub_ratCast (h : Irrational (x - q)) : Irrational x :=
  of_add_ratCast (-q) <| by simpa only [cast_neg, sub_eq_add_neg] using h
theorem of_ratCast_sub (h : Irrational (q - x)) : Irrational x :=
  of_neg (of_ratCast_add q (by simpa only [sub_eq_add_neg] using h))
theorem sub_intCast (h : Irrational x) (m : ℤ) : Irrational (x - m) := by sorry
theorem intCast_sub (h : Irrational x) (m : ℤ) : Irrational (m - x) := by sorry
theorem of_sub_intCast (m : ℤ) (h : Irrational (x - m)) : Irrational x :=
  of_sub_ratCast m <| by rwa [Rat.cast_intCast]
theorem of_intCast_sub (m : ℤ) (h : Irrational (m - x)) : Irrational x :=
  of_ratCast_sub m <| by rwa [Rat.cast_intCast]
theorem sub_natCast (h : Irrational x) (m : ℕ) : Irrational (x - m) :=
  h.sub_intCast m
theorem natCast_sub (h : Irrational x) (m : ℕ) : Irrational (m - x) :=
  h.intCast_sub m
theorem of_sub_natCast (m : ℕ) (h : Irrational (x - m)) : Irrational x :=
  h.of_sub_intCast m
theorem of_natCast_sub (m : ℕ) (h : Irrational (m - x)) : Irrational x :=
  h.of_intCast_sub m
/-!
#### Multiplication by rational numbers
-/


theorem mul_cases : Irrational (x * y) → Irrational x ∨ Irrational y := by sorry
theorem of_mul_ratCast (h : Irrational (x * q)) : Irrational x :=
  h.mul_cases.resolve_right q.not_irrational
theorem mul_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x * q) :=
  of_mul_ratCast q⁻¹ <| by rwa [mul_assoc, ← cast_mul, mul_inv_cancel₀ hq, cast_one, mul_one]
theorem of_ratCast_mul : Irrational (q * x) → Irrational x :=
  mul_comm x q ▸ of_mul_ratCast q
theorem ratCast_mul (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q * x) :=
  mul_comm x q ▸ h.mul_ratCast hq
theorem of_mul_intCast (m : ℤ) (h : Irrational (x * m)) : Irrational x :=
  of_mul_ratCast m <| by rwa [cast_intCast]
theorem of_intCast_mul (m : ℤ) (h : Irrational (m * x)) : Irrational x :=
  of_ratCast_mul m <| by rwa [cast_intCast]
theorem mul_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x * m) := by sorry
theorem intCast_mul (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m * x) :=
  mul_comm x m ▸ h.mul_intCast hm
theorem of_mul_natCast (m : ℕ) (h : Irrational (x * m)) : Irrational x :=
  h.of_mul_intCast m
theorem of_natCast_mul (m : ℕ) (h : Irrational (m * x)) : Irrational x :=
  h.of_intCast_mul m
theorem mul_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x * m) :=
  h.mul_intCast <| Int.natCast_ne_zero.2 hm
theorem natCast_mul (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m * x) :=
  h.intCast_mul <| Int.natCast_ne_zero.2 hm
/-!
#### Inverse
-/


theorem of_inv (h : Irrational x⁻¹) : Irrational x := fun ⟨q, hq⟩ => h <| hq ▸ ⟨q⁻¹, q.cast_inv⟩

protected theorem inv (h : Irrational x) : Irrational x⁻¹ :=
  of_inv <| by rwa [inv_inv]

/-!
#### Division
-/


theorem div_cases (h : Irrational (x / y)) : Irrational x ∨ Irrational y :=
  h.mul_cases.imp id of_inv

theorem of_ratCast_div (h : Irrational (q / x)) : Irrational x :=
  (h.of_ratCast_mul q).of_inv
theorem of_div_ratCast (h : Irrational (x / q)) : Irrational x :=
  h.div_cases.resolve_right q.not_irrational
theorem ratCast_div (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (q / x) :=
  h.inv.ratCast_mul hq
theorem div_ratCast (h : Irrational x) {q : ℚ} (hq : q ≠ 0) : Irrational (x / q) := by sorry
theorem of_intCast_div (m : ℤ) (h : Irrational (m / x)) : Irrational x :=
  h.div_cases.resolve_left m.not_irrational
theorem of_div_intCast (m : ℤ) (h : Irrational (x / m)) : Irrational x :=
  h.div_cases.resolve_right m.not_irrational
theorem intCast_div (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.intCast_mul hm
theorem div_intCast (h : Irrational x) {m : ℤ} (hm : m ≠ 0) : Irrational (x / m) := by sorry
theorem of_natCast_div (m : ℕ) (h : Irrational (m / x)) : Irrational x :=
  h.of_intCast_div m
theorem of_div_natCast (m : ℕ) (h : Irrational (x / m)) : Irrational x :=
  h.of_div_intCast m
theorem natCast_div (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (m / x) :=
  h.inv.natCast_mul hm
theorem div_natCast (h : Irrational x) {m : ℕ} (hm : m ≠ 0) : Irrational (x / m) :=
  h.div_intCast <| by rwa [Int.natCast_ne_zero]
theorem of_one_div (h : Irrational (1 / x)) : Irrational x :=
  of_ratCast_div 1 <| by rwa [cast_one]

/-!
#### Natural and integer power
-/


theorem of_mul_self (h : Irrational (x * x)) : Irrational x :=
  h.mul_cases.elim id id

theorem of_pow : ∀ n : ℕ, Irrational (x ^ n) → Irrational x := by sorry
open Int in
theorem of_zpow : ∀ m : ℤ, Irrational (x ^ m) → Irrational x := by sorry
end Irrational

section Polynomial

open Polynomial

variable (x : ℝ) (p : ℤ[X])

theorem one_lt_natDegree_of_irrational_root (hx : Irrational x) (p_nonzero : p ≠ 0)
    (x_is_root : aeval x p = 0) : 1 < p.natDegree := by sorry
end Polynomial

section

variable {q : ℚ} {m : ℤ} {n : ℕ} {x : ℝ}

open Irrational

/-!
### Simplification lemmas about operations
-/


@[simp]
theorem irrational_ratCast_add_iff : Irrational (q + x) ↔ Irrational x :=
  ⟨of_ratCast_add q, ratCast_add q⟩
@[simp]
theorem irrational_intCast_add_iff : Irrational (m + x) ↔ Irrational x :=
  ⟨of_intCast_add m, fun h => h.intCast_add m⟩
@[simp]
theorem irrational_natCast_add_iff : Irrational (n + x) ↔ Irrational x :=
  ⟨of_natCast_add n, fun h => h.natCast_add n⟩
@[simp]
theorem irrational_add_ratCast_iff : Irrational (x + q) ↔ Irrational x :=
  ⟨of_add_ratCast q, add_ratCast q⟩
@[simp]
theorem irrational_add_intCast_iff : Irrational (x + m) ↔ Irrational x :=
  ⟨of_add_intCast m, fun h => h.add_intCast m⟩
@[simp]
theorem irrational_add_natCast_iff : Irrational (x + n) ↔ Irrational x :=
  ⟨of_add_natCast n, fun h => h.add_natCast n⟩
@[simp]
theorem irrational_ratCast_sub_iff : Irrational (q - x) ↔ Irrational x :=
  ⟨of_ratCast_sub q, ratCast_sub q⟩
@[simp]
theorem irrational_intCast_sub_iff : Irrational (m - x) ↔ Irrational x :=
  ⟨of_intCast_sub m, fun h => h.intCast_sub m⟩
@[simp]
theorem irrational_natCast_sub_iff : Irrational (n - x) ↔ Irrational x :=
  ⟨of_natCast_sub n, fun h => h.natCast_sub n⟩
@[simp]
theorem irrational_sub_ratCast_iff : Irrational (x - q) ↔ Irrational x :=
  ⟨of_sub_ratCast q, sub_ratCast q⟩
@[simp]
theorem irrational_sub_intCast_iff : Irrational (x - m) ↔ Irrational x :=
  ⟨of_sub_intCast m, fun h => h.sub_intCast m⟩
@[simp]
theorem irrational_sub_natCast_iff : Irrational (x - n) ↔ Irrational x :=
  ⟨of_sub_natCast n, fun h => h.sub_natCast n⟩
@[simp]
theorem irrational_neg_iff : Irrational (-x) ↔ Irrational x :=
  ⟨of_neg, Irrational.neg⟩

@[simp]
theorem irrational_inv_iff : Irrational x⁻¹ ↔ Irrational x :=
  ⟨of_inv, Irrational.inv⟩

@[simp]
theorem irrational_ratCast_mul_iff : Irrational (q * x) ↔ q ≠ 0 ∧ Irrational x :=
  ⟨fun h => ⟨Rat.cast_ne_zero.1 <| left_ne_zero_of_mul h.ne_zero, h.of_ratCast_mul q⟩, fun h =>
    h.2.ratCast_mul h.1⟩
@[simp]
theorem irrational_mul_ratCast_iff : Irrational (x * q) ↔ q ≠ 0 ∧ Irrational x := by sorry
theorem irrational_intCast_mul_iff : Irrational (m * x) ↔ m ≠ 0 ∧ Irrational x := by sorry
theorem irrational_mul_intCast_iff : Irrational (x * m) ↔ m ≠ 0 ∧ Irrational x := by sorry
theorem irrational_natCast_mul_iff : Irrational (n * x) ↔ n ≠ 0 ∧ Irrational x := by sorry
theorem irrational_mul_natCast_iff : Irrational (x * n) ↔ n ≠ 0 ∧ Irrational x := by sorry
theorem irrational_ratCast_div_iff : Irrational (q / x) ↔ q ≠ 0 ∧ Irrational x := by sorry
theorem irrational_div_ratCast_iff : Irrational (x / q) ↔ q ≠ 0 ∧ Irrational x := by sorry
theorem irrational_intCast_div_iff : Irrational (m / x) ↔ m ≠ 0 ∧ Irrational x := by sorry
theorem irrational_div_intCast_iff : Irrational (x / m) ↔ m ≠ 0 ∧ Irrational x := by sorry
theorem irrational_natCast_div_iff : Irrational (n / x) ↔ n ≠ 0 ∧ Irrational x := by sorry
theorem irrational_div_natCast_iff : Irrational (x / n) ↔ n ≠ 0 ∧ Irrational x := by sorry
theorem exists_irrational_btwn {x y : ℝ} (h : x < y) : ∃ r, Irrational r ∧ x < r ∧ r < y :=
  let ⟨q, ⟨hq1, hq2⟩⟩ := exists_rat_btwn ((sub_lt_sub_iff_right (√2)).mpr h)
  ⟨q + √2, irrational_sqrt_two.ratCast_add _, sub_lt_iff_lt_add.mp hq1, lt_sub_iff_add_lt.mp hq2⟩

end
