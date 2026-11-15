/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Semiconj
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Basic
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcdA x y` and `gcdB x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcdA x y + y * gcdB x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/

@[expose] public section

/-! ### Extended Euclidean algorithm -/


namespace Nat

/-- Helper function for the extended GCD algorithm (`Nat.xgcd`). -/
def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ :=
  Nat.strongRec' fun n ih s t r' s' t' ↦ match n with
  | 0 => (r', s', t')
  | succ k =>
    let q := r' / succ k
    ih (r' % succ k) (mod_lt _ <| (succ_pos _).gt) (s' - q * s) (t' - q * t) (succ k) s t

@[simp]
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := rfl

theorem xgcdAux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by sorry
def xgcd (x y : ℕ) : ℤ × ℤ :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : ℕ) : ℤ :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : ℕ) : ℤ :=
  (xgcd x y).2

@[simp]
theorem gcdA_zero_left {s : ℕ} : gcdA 0 s = 0 := rfl

@[simp]
theorem gcdB_zero_left {s : ℕ} : gcdB 0 s = 1 := rfl

@[simp]
theorem gcdA_zero_right {s : ℕ} (h : s ≠ 0) : gcdA s 0 = 1 := by sorry
theorem gcdB_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by sorry
theorem xgcdAux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]

theorem xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by sorry
theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by sorry
variable (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
  | (r, s, t) => (r : ℤ) = x * s + y * t

private theorem xgcdAux_P {r r'} :
    ∀ {s t s' t'}, P x y (r, s, t) → P x y (r', s', t') → P x y (xgcdAux r s t r' s' t') := by sorry
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by sorry
end

theorem exists_mul_mod_eq_gcd {k n : ℕ} (hk : gcd n k < k) : ∃ m < k, n * m % k = gcd n k := by sorry
theorem exists_mul_mod_eq_one_of_coprime {k n : ℕ} (hkn : Coprime n k) (hk : 1 < k) :
    ∃ m < k, n * m % k = 1 := by sorry
theorem exists_mul_mod_eq_of_coprime {k n : ℕ} (r : ℕ) (hkn : Coprime n k) (hk : k ≠ 0) :
    ∃ m < k, n * m % k = r % k := by sorry
end Nat

/-! ### Divisibility over ℤ -/


namespace Int

theorem gcd_def (i j : ℤ) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA : ℤ → ℤ → ℤ
  | ofNat m, n => m.gcdA n.natAbs
  | -[m+1], n => -m.succ.gcdA n.natAbs

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB : ℤ → ℤ → ℤ
  | m, ofNat n => m.natAbs.gcdB n
  | m, -[n+1] => -m.natAbs.gcdB n.succ

/-- **Bézout's lemma** -/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by sorry
theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd

/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_right_right a m n

/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_left_right a n m

theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by sorry
theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
    ∃ m' n' : ℤ, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

theorem gcd_dvd_iff {a b : ℤ} {n : ℕ} : gcd a b ∣ n ↔ ∃ x y : ℤ, ↑n = a * x + b * y := by sorry
theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (natCast_nonneg (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `IsCoprime.dvd_of_dvd_mul_left` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a c = 1) :
    a ∣ b := by sorry
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a b = 1) :
    a ∣ c := by sorry
theorem gcd_least_linear {a b : ℤ} (ha : a ≠ 0) :
    IsLeast { n : ℕ | 0 < n ∧ ∃ x y : ℤ, ↑n = a * x + b * y } (a.gcd b) := by sorry
end Int

section Monoid
variable {M : Type*} [Monoid M] {a : M} {m n : ℕ}

@[to_additive (attr := simp) gcd_nsmul_eq_zero]
lemma pow_gcd_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 where
  mp hmn := by sorry
lemma pow_eq_one_iff_of_coprime (hmn : m.Coprime n) : a ^ m = 1 ∧ a ^ n = 1 ↔ a = 1 := by sorry
end Monoid

section Group
variable {M : Type*} [Group M] {a : M} {m n : ℤ}

@[to_additive (attr := simp) intGCD_nsmul_eq_zero]
lemma pow_intGCD_eq_one : a ^ m.gcd n = 1 ↔ a ^ m = 1 ∧ a ^ n = 1 := by sorry
end Group

variable {α : Type*}

section GroupWithZero
variable [GroupWithZero α] {a b : α} {m n : ℕ}

protected lemma Commute.pow_eq_pow_iff_of_coprime (hab : Commute a b) (hmn : m.Coprime n) :
    a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m := by sorry
end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero α] {a b : α} {m n : ℕ}

lemma pow_eq_pow_iff_of_coprime (hmn : m.Coprime n) : a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m :=
  (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn

lemma pow_mem_range_pow_of_coprime (hmn : m.Coprime n) (a : α) :
    a ^ m ∈ Set.range (· ^ n : α → α) ↔ a ∈ Set.range (· ^ n : α → α) := by sorry
end CommGroupWithZero
