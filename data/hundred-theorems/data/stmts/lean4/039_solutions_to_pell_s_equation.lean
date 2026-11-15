/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Pell's equation and Matiyasevic's theorem

This file solves Pell's equation, i.e. integer solutions to `x ^ 2 - d * y ^ 2 = 1`
*in the special case that `d = a ^ 2 - 1`*.
This is then applied to prove Matiyasevic's theorem that the power
function is Diophantine, which is the last key ingredient in the solution to Hilbert's tenth
problem. For the definition of Diophantine function, see `NumberTheory.Dioph`.

For results on Pell's equation for arbitrary (positive, non-square) `d`, see
`NumberTheory.Pell`.

## Main definition

* `pell` is a function assigning to a natural number `n` the `n`-th solution to Pell's equation
  constructed recursively from the initial solution `(0, 1)`.

## Main statements

* `eq_pell` shows that every solution to Pell's equation is recursively obtained using `pell`
* `matiyasevic` shows that a certain system of Diophantine equations has a solution if and only if
  the first variable is the `x`-component in a solution to Pell's equation - the key step towards
  Hilbert's tenth problem in Davis' version of Matiyasevic's theorem.
* `eq_pow_of_pell` shows that the power function is Diophantine.

## Implementation notes

The proof of Matiyasevic's theorem doesn't follow Matiyasevic's original account of using Fibonacci
numbers but instead Davis' variant of using solutions to Pell's equation.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevič's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Pell's equation, Matiyasevic's theorem, Hilbert's tenth problem

-/

@[expose] public section


namespace Pell

open Nat

section

variable {d : ℤ}

/-- The property of being a solution to the Pell equation, expressed
  as a property of elements of `ℤ√d`. -/
def IsPell : ℤ√d → Prop
  | ⟨x, y⟩ => x * x - d * y * y = 1

theorem isPell_norm : ∀ {b : ℤ√d}, IsPell b ↔ b * star b = 1 := by sorry
theorem isPell_iff_mem_unitary : ∀ {b : ℤ√d}, IsPell b ↔ b ∈ unitary (ℤ√d) := by sorry
theorem isPell_mul {b c : ℤ√d} (hb : IsPell b) (hc : IsPell c) : IsPell (b * c) :=
  isPell_norm.2 (by simp [mul_comm, mul_left_comm c, mul_assoc,
    star_mul, isPell_norm.1 hb, isPell_norm.1 hc])

theorem isPell_star : ∀ {b : ℤ√d}, IsPell b ↔ IsPell (star b) := by sorry
end

section

variable {a : ℕ} (a1 : 1 < a)

set_option backward.privateInPublic true in
private def d (_a1 : 1 < a) :=
  a * a - 1

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
theorem d_pos : 0 < d a1 :=
  tsub_pos_of_lt (mul_lt_mul a1 (le_of_lt a1) (by decide) (Nat.zero_le _) : 1 * 1 < a * a)

-- TODO(lint): Fix double namespace issue
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Pell sequences, i.e. the sequence of integer solutions to `x ^ 2 - d * y ^ 2 = 1`, where
`d = a ^ 2 - 1`, defined together in mutual recursion. -/
--@[nolint dup_namespace]
def pell : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => ((pell n).1 * a + d a1 * (pell n).2, (pell n).1 + (pell n).2 * a)

/-- The Pell `x` sequence. -/
def xn (n : ℕ) : ℕ :=
  (pell a1 n).1

/-- The Pell `y` sequence. -/
def yn (n : ℕ) : ℕ :=
  (pell a1 n).2

@[simp]
theorem pell_val (n : ℕ) : pell a1 n = (xn a1 n, yn a1 n) :=
  show pell a1 n = ((pell a1 n).1, (pell a1 n).2) from
    match pell a1 n with := by sorry
theorem xn_zero : xn a1 0 = 1 :=
  rfl

@[simp]
theorem yn_zero : yn a1 0 = 0 :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
theorem xn_succ (n : ℕ) : xn a1 (n + 1) = xn a1 n * a + d a1 * yn a1 n :=
  rfl

@[simp]
theorem yn_succ (n : ℕ) : yn a1 (n + 1) = xn a1 n + yn a1 n * a :=
  rfl

theorem xn_one : xn a1 1 = a := by simp

theorem yn_one : yn a1 1 = 1 := by simp

/-- The Pell `x` sequence, considered as an integer sequence. -/
def xz (n : ℕ) : ℤ :=
  xn a1 n

/-- The Pell `y` sequence, considered as an integer sequence. -/
def yz (n : ℕ) : ℤ :=
  yn a1 n

section

/-- The element `a` such that `d = a ^ 2 - 1`, considered as an integer. -/
def az (a : ℕ) : ℤ :=
  a

end

include a1 in
theorem asq_pos : 0 < a * a :=
  le_trans (le_of_lt a1)
    (by have := @Nat.mul_le_mul_left 1 a a (le_of_lt a1); rwa [mul_one] at this)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem dz_val : ↑(d a1) = az a * az a - 1 :=
  have : 1 ≤ a * a := asq_pos a1
  by rw [Pell.d, Int.ofNat_sub this]; rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
theorem xz_succ (n : ℕ) : (xz a1 (n + 1)) = xz a1 n * az a + d a1 * yz a1 n :=
  rfl

@[simp]
theorem yz_succ (n : ℕ) : yz a1 (n + 1) = xz a1 n + yz a1 n * az a :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Pell sequence can also be viewed as an element of `ℤ√d` -/
def pellZd (n : ℕ) : ℤ√(d a1) :=
  ⟨xn a1 n, yn a1 n⟩

@[simp]
theorem re_pellZd (n : ℕ) : (pellZd a1 n).re = xn a1 n :=
  rfl

@[simp]
theorem im_pellZd (n : ℕ) : (pellZd a1 n).im = yn a1 n :=
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem isPell_nat {x y : ℕ} : IsPell (⟨x, y⟩ : ℤ√(d a1)) ↔ x * x - d a1 * y * y = 1 :=
  ⟨fun h =>
    (Nat.cast_inj (R := ℤ)).1
      (by rw [Int.ofNat_sub (Int.le_of_ofNat_le_ofNat <| Int.le.intro_sub _ h)]; exact h),
    fun h =>
    show ((x * x : ℕ) - (d a1 * y * y : ℕ) : ℤ) = 1 by
      rw [← Int.ofNat_sub <| le_of_lt <| Nat.lt_of_sub_eq_succ h, h]; rfl⟩

@[simp]
theorem pellZd_succ (n : ℕ) : pellZd a1 (n + 1) = pellZd a1 n * ⟨a, 1⟩ := by ext <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem isPell_one : IsPell (⟨a, 1⟩ : ℤ√(d a1)) :=
  show az a * az a - d a1 * 1 * 1 = 1 by simp [dz_val]

theorem isPell_pellZd : ∀ n : ℕ, IsPell (pellZd a1 n) := by sorry
theorem pell_eqz (n : ℕ) : xz a1 n * xz a1 n - d a1 * yz a1 n * yz a1 n = 1 :=
  isPell_pellZd a1 n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
theorem pell_eq (n : ℕ) : xn a1 n * xn a1 n - d a1 * yn a1 n * yn a1 n = 1 :=
  let pn := pell_eqz a1 n
  have h : (↑(xn a1 n * xn a1 n) : ℤ) - ↑(d a1 * yn a1 n * yn a1 n) = 1 := by sorry
instance dnsq : Zsqrtd.Nonsquare (d a1) :=
  ⟨fun n h =>
    have : n * n + 1 = a * a := by rw [← h]; exact Nat.succ_pred_eq_of_pos (asq_pos a1)
    have na : n < a := Nat.mul_self_lt_mul_self_iff.1 (by rw [← this]; exact Nat.lt_succ_self _)
    have : (n + 1) * (n + 1) ≤ n * n + 1 := by rw [this]; exact Nat.mul_self_le_mul_self na
    have : n + n ≤ 0 :=
      @Nat.le_of_add_le_add_right _ (n * n + 1) _ (by ring_nf at this ⊢; assumption)
    Nat.ne_of_gt (d_pos a1) <| by
      rwa [Nat.eq_zero_of_le_zero ((Nat.le_add_left _ _).trans this)] at h⟩

theorem xn_ge_a_pow : ∀ n : ℕ, a ^ n ≤ xn a1 n := by sorry
theorem n_lt_xn (n) : n < xn a1 n :=
  lt_of_lt_of_le (Nat.lt_pow_self a1) (xn_ge_a_pow a1 n)

theorem x_pos (n) : 0 < xn a1 n :=
  lt_of_le_of_lt (Nat.zero_le n) (n_lt_xn a1 n)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem eq_pell_lem : ∀ (n) (b : ℤ√(d a1)), 1 ≤ b → IsPell b →
    b ≤ pellZd a1 n → ∃ n, b = pellZd a1 n := by sorry
theorem eq_pellZd (b : ℤ√(d a1)) (b1 : 1 ≤ b) (hp : IsPell b) : ∃ n, b = pellZd a1 n :=
  let ⟨n, h⟩ := @Zsqrtd.le_arch (d a1) b
  eq_pell_lem a1 n b b1 hp <|
    h.trans <| by
      rw [Zsqrtd.natCast_val]
      exact
        Zsqrtd.le_of_le_le (Int.ofNat_le_ofNat_of_le <| le_of_lt <| n_lt_xn _ _)
          (Int.natCast_nonneg _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Every solution to **Pell's equation** is recursively obtained from the initial solution
`(1,0)` using the recursion `pell`. -/
theorem eq_pell {x y : ℕ} (hp : x * x - d a1 * y * y = 1) : ∃ n, x = xn a1 n ∧ y = yn a1 n :=
  have : (1 : ℤ√(d a1)) ≤ ⟨x, y⟩ :=
    match x, hp with := by sorry
theorem pellZd_add (m) : ∀ n, pellZd a1 (m + n) = pellZd a1 m * pellZd a1 n := by sorry
theorem xn_add (m n) : xn a1 (m + n) = xn a1 m * xn a1 n + d a1 * yn a1 m * yn a1 n := by sorry
theorem yn_add (m n) : yn a1 (m + n) = xn a1 m * yn a1 n + yn a1 m * xn a1 n := by sorry
theorem pellZd_sub {m n} (h : n ≤ m) : pellZd a1 (m - n) = pellZd a1 m * star (pellZd a1 n) := by sorry
theorem xz_sub {m n} (h : n ≤ m) :
    xz a1 (m - n) = xz a1 m * xz a1 n - d a1 * yz a1 m * yz a1 n := by sorry
theorem yz_sub {m n} (h : n ≤ m) : yz a1 (m - n) = xz a1 n * yz a1 m - xz a1 m * yz a1 n := by sorry
theorem xy_coprime (n) : (xn a1 n).Coprime (yn a1 n) :=
  Nat.coprime_of_dvd' fun k _ kx ky => by
    let p := pell_eq a1 n
    rw [← p]
    exact Nat.dvd_sub (kx.mul_left _) (ky.mul_left _)

theorem strictMono_y : StrictMono (yn a1) := by sorry
theorem strictMono_x : StrictMono (xn a1) := by sorry
theorem yn_ge_n : ∀ n, n ≤ yn a1 n := by sorry
theorem y_mul_dvd (n) : ∀ k, yn a1 n ∣ yn a1 (n * k) := by sorry
theorem y_dvd_iff (m n) : yn a1 m ∣ yn a1 n ↔ m ∣ n :=
  ⟨fun h =>
    Nat.dvd_of_mod_eq_zero <|
      (Nat.eq_zero_or_pos _).resolve_right fun hp => by
        have co : Nat.Coprime (yn a1 m) (xn a1 (m * (n / m))) :=
          Nat.Coprime.symm <| (xy_coprime a1 _).coprime_dvd_right (y_mul_dvd a1 m (n / m))
        have m0 : 0 < m :=
          m.eq_zero_or_pos.resolve_left fun e => by
            rw [e, Nat.mod_zero] at hp;rw [e] at h
            exact _root_.ne_of_lt (strictMono_y a1 hp) (eq_zero_of_zero_dvd h).symm
        rw [← Nat.mod_add_div n m, yn_add] at h
        exact
          not_le_of_gt (strictMono_y _ <| Nat.mod_lt n m0)
            (Nat.le_of_dvd (strictMono_y _ hp) <|
              co.dvd_of_dvd_mul_right <|
                (Nat.dvd_add_iff_right <| (y_mul_dvd _ _ _).mul_left _).2 h),
    fun ⟨k, e⟩ => by rw [e]; apply y_mul_dvd⟩

theorem xy_modEq_yn (n) :
    ∀ k, xn a1 (n * k) ≡ xn a1 n ^ k [MOD yn a1 n ^ 2] ∧ yn a1 (n * k) ≡
        k * xn a1 n ^ (k - 1) * yn a1 n [MOD yn a1 n ^ 3] := by sorry
theorem ysq_dvd_yy (n) : yn a1 n * yn a1 n ∣ yn a1 (n * yn a1 n) :=
  modEq_zero_iff_dvd.1 <|
    ((xy_modEq_yn a1 n (yn a1 n)).right.of_dvd <| by simp [_root_.pow_succ]).trans
      (modEq_zero_iff_dvd.2 <| by simp [mul_dvd_mul_left, mul_assoc])

theorem dvd_of_ysq_dvd {n t} (h : yn a1 n * yn a1 n ∣ yn a1 t) : yn a1 n ∣ t :=
  have nt : n ∣ t := (y_dvd_iff a1 n t).1 <| dvd_of_mul_left_dvd h
  n.eq_zero_or_pos.elim (fun n0 => by rwa [n0] at nt ⊢) fun n0l : 0 < n => by
    let ⟨k, ke⟩ := nt
    have : yn a1 n ∣ k * xn a1 n ^ (k - 1) :=
      Nat.dvd_of_mul_dvd_mul_right (strictMono_y a1 n0l) <|
        modEq_zero_iff_dvd.1 <| by
          have xm := (xy_modEq_yn a1 n k).right; rw [← ke] at xm
          exact (xm.of_dvd <| by simp [_root_.pow_succ]).symm.trans h.modEq_zero_nat
    rw [ke]
    exact dvd_mul_of_dvd_right (((xy_coprime _ _).pow_left _).symm.dvd_of_dvd_mul_right this) _

set_option backward.isDefEq.respectTransparency false in
theorem pellZd_succ_succ (n) :
    pellZd a1 (n + 2) + pellZd a1 n = (2 * a : ℕ) * pellZd a1 (n + 1) := by sorry
theorem xy_succ_succ (n) :
    xn a1 (n + 2) + xn a1 n =
      2 * a * xn a1 (n + 1) ∧ yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) := by sorry
theorem xn_succ_succ (n) : xn a1 (n + 2) + xn a1 n = 2 * a * xn a1 (n + 1) :=
  (xy_succ_succ a1 n).1

theorem yn_succ_succ (n) : yn a1 (n + 2) + yn a1 n = 2 * a * yn a1 (n + 1) :=
  (xy_succ_succ a1 n).2

theorem xz_succ_succ (n) : xz a1 (n + 2) = (2 * a : ℕ) * xz a1 (n + 1) - xz a1 n :=
  eq_sub_of_add_eq <| by delta xz; rw [← Int.natCast_add, ← Int.natCast_mul, xn_succ_succ]

theorem yz_succ_succ (n) : yz a1 (n + 2) = (2 * a : ℕ) * yz a1 (n + 1) - yz a1 n :=
  eq_sub_of_add_eq <| by delta yz; rw [← Int.natCast_add, ← Int.natCast_mul, yn_succ_succ]

theorem yn_modEq_a_sub_one : ∀ n, yn a1 n ≡ n [MOD a - 1] := by sorry
theorem yn_modEq_two : ∀ n, yn a1 n ≡ n [MOD 2] := by sorry
theorem x_sub_y_dvd_pow_lem (y2 y1 y0 yn1 yn0 xn1 xn0 ay a2 : ℤ) :
    (a2 * yn1 - yn0) * ay + y2 - (a2 * xn1 - xn0) =
      y2 - a2 * y1 + y0 + a2 * (yn1 * ay + y1 - xn1) - (yn0 * ay + y0 - xn0) := by sorry
end

theorem x_sub_y_dvd_pow (y : ℕ) :
    ∀ n, (2 * a * y - y * y - 1 : ℤ) ∣ yz a1 n * (a - y) + ↑(y ^ n) - xz a1 n := by sorry
theorem xn_modEq_x2n_add_lem (n j) : xn a1 n ∣ d a1 * yn a1 n * (yn a1 n * xn a1 j) + xn a1 j := by sorry
theorem xn_modEq_x2n_add (n j) : xn a1 (2 * n + j) + xn a1 j ≡ 0 [MOD xn a1 n] := by sorry
theorem xn_modEq_x2n_sub_lem {n j} (h : j ≤ n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] := by sorry
theorem xn_modEq_x2n_sub {n j} (h : j ≤ 2 * n) : xn a1 (2 * n - j) + xn a1 j ≡ 0 [MOD xn a1 n] :=
  (le_total j n).elim (xn_modEq_x2n_sub_lem a1) fun jn => by
    have : 2 * n - j + j ≤ n + j := by sorry
theorem xn_modEq_x4n_add (n j) : xn a1 (4 * n + j) ≡ xn a1 j [MOD xn a1 n] :=
  ModEq.add_right_cancel' (xn a1 (2 * n + j)) <| by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_add _ _ _).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_assoc]
    apply xn_modEq_x2n_add

theorem xn_modEq_x4n_sub {n j} (h : j ≤ 2 * n) : xn a1 (4 * n - j) ≡ xn a1 j [MOD xn a1 n] :=
  have h' : j ≤ 2 * n := le_trans h (by rw [Nat.succ_mul])
  ModEq.add_right_cancel' (xn a1 (2 * n - j)) <| by
    refine @ModEq.trans _ _ 0 _ ?_ (by rw [add_comm]; exact (xn_modEq_x2n_sub _ h).symm)
    rw [show 4 * n = 2 * n + 2 * n from right_distrib 2 2 n, add_tsub_assoc_of_le h']
    apply xn_modEq_x2n_add

theorem eq_of_xn_modEq_lem1 {i n} : ∀ {j}, i < j → j < n → xn a1 i % xn a1 n < xn a1 j % xn a1 n := by sorry
theorem eq_of_xn_modEq_lem2 {n} (h : 2 * xn a1 n = xn a1 (n + 1)) : a = 2 ∧ n = 0 := by sorry
theorem eq_of_xn_modEq_lem3 {i n} (npos : 0 < n) :
    ∀ {j}, i < j → j ≤ 2 * n → j ≠ n → ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2) →
        xn a1 i % xn a1 n < xn a1 j % xn a1 n := by sorry
theorem eq_of_xn_modEq_le {i j n} (ij : i ≤ j) (j2n : j ≤ 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : ¬(a = 2 ∧ n = 1 ∧ i = 0 ∧ j = 2)) : i = j :=
  if npos : n = 0 then by simp_all
  else
    (lt_or_eq_of_le ij).resolve_left fun ij' =>
      if jn : j = n then by
        refine _root_.ne_of_gt ?_ h
        rw [jn, Nat.mod_self]
        have x0 : 0 < xn a1 0 % xn a1 n := by sorry
theorem eq_of_xn_modEq {i j n} (i2n : i ≤ 2 * n) (j2n : j ≤ 2 * n)
    (h : xn a1 i ≡ xn a1 j [MOD xn a1 n])
    (ntriv : a = 2 → n = 1 → (i = 0 → j ≠ 2) ∧ (i = 2 → j ≠ 0)) : i = j :=
  (le_total i j).elim
    (fun ij => eq_of_xn_modEq_le a1 ij j2n h fun ⟨a2, n1, i0, j2⟩ => (ntriv a2 n1).left i0 j2)
    fun ij =>
    (eq_of_xn_modEq_le a1 ij i2n h.symm fun ⟨a2, n1, j0, i2⟩ => (ntriv a2 n1).right i2 j0).symm

theorem eq_of_xn_modEq' {i j n} (ipos : 0 < i) (hin : i ≤ n) (j4n : j ≤ 4 * n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) : j = i ∨ j + i = 4 * n :=
  have i2n : i ≤ 2 * n := by apply le_trans hin; rw [two_mul]; apply Nat.le_add_left
  (le_or_gt j (2 * n)).imp
    (fun j2n : j ≤ 2 * n =>
      eq_of_xn_modEq a1 j2n i2n h fun _ n1 =>
        ⟨fun _ i2 => by rw [n1, i2] at hin; exact absurd hin (by decide), fun _ i0 =>
          _root_.ne_of_gt ipos i0⟩)
    fun j2n : 2 * n < j =>
    suffices i = 4 * n - j by rw [this, add_tsub_cancel_of_le j4n]
    have j42n : 4 * n - j ≤ 2 * n := by lia
    eq_of_xn_modEq a1 i2n j42n
      (h.symm.trans <| by
        let t := xn_modEq_x4n_sub a1 j42n
        rwa [tsub_tsub_cancel_of_le j4n] at t)
      (by lia)

theorem modEq_of_xn_modEq {i j n} (ipos : 0 < i) (hin : i ≤ n)
    (h : xn a1 j ≡ xn a1 i [MOD xn a1 n]) :
    j ≡ i [MOD 4 * n] ∨ j + i ≡ 0 [MOD 4 * n] :=
  let j' := j % (4 * n)
  have n4 : 0 < 4 * n := mul_pos (by decide) (ipos.trans_le hin)
  have jl : j' < 4 * n := Nat.mod_lt _ n4
  have jj : j ≡ j' [MOD 4 * n] := by delta ModEq; rw [Nat.mod_eq_of_lt jl]
  have : ∀ j q, xn a1 (j + 4 * n * q) ≡ xn a1 j [MOD xn a1 n] := by sorry
end

theorem xy_modEq_of_modEq {a b c} (a1 : 1 < a) (b1 : 1 < b) (h : a ≡ b [MOD c]) :
    ∀ n, xn a1 n ≡ xn b1 n [MOD c] ∧ yn a1 n ≡ yn b1 n [MOD c] := by sorry
theorem matiyasevic {a k x y} :
    (∃ a1 : 1 < a, xn a1 k = x ∧ yn a1 k = y) ↔
      1 < a ∧ k ≤ y ∧ (x = 1 ∧ y = 0 ∨
        ∃ u v s t b : ℕ,
          x * x - (a * a - 1) * y * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧
          s * s - (b * b - 1) * t * t = 1 ∧ 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧
          b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t ≡ k [MOD 4 * y]) :=
  ⟨fun ⟨a1, hx, hy⟩ => by
    rw [← hx, ← hy]
    refine ⟨a1,
        (Nat.eq_zero_or_pos k).elim (fun k0 => by rw [k0]; exact ⟨le_rfl, Or.inl ⟨rfl, rfl⟩⟩)
          fun kpos => ?_⟩
    exact
      let x := xn a1 k
      let y := yn a1 k
      let m := 2 * (k * y)
      let u := xn a1 m
      let v := yn a1 m
      have ky : k ≤ y := yn_ge_n a1 k
      have yv : y * y ∣ v := (ysq_dvd_yy a1 k).trans <| (y_dvd_iff _ _ _).2 <| dvd_mul_left _ _
      have uco : Nat.Coprime u (4 * y) :=
        have : 2 ∣ v :=
          modEq_zero_iff_dvd.1 <| (yn_modEq_two _ _).trans (dvd_mul_right _ _).modEq_zero_nat
        have : Nat.Coprime u 2 := (xy_coprime a1 m).coprime_dvd_right this
        (this.mul_right this).mul_right <|
          (xy_coprime _ _).coprime_dvd_right (dvd_of_mul_left_dvd yv)
      let ⟨b, ba, bm1⟩ := chineseRemainder uco a 1
      have m1 : 1 < m :=
        have : 0 < k * y := mul_pos kpos (strictMono_y a1 kpos)
        Nat.mul_le_mul_left 2 this
      have vp : 0 < v := strictMono_y a1 (lt_trans zero_lt_one m1)
      have b1 : 1 < b :=
        have : xn a1 1 < u := strictMono_x a1 m1
        have : a < u := by simpa using this
        lt_of_lt_of_le a1 <| by
          delta ModEq at ba; rw [Nat.mod_eq_of_lt this] at ba; rw [← ba]
          apply Nat.mod_le
      let s := xn b1 k
      let t := yn b1 k
      have sx : s ≡ x [MOD u] := (xy_modEq_of_modEq b1 a1 ba k).left
      have tk : t ≡ k [MOD 4 * y] :=
        have : 4 * y ∣ b - 1 :=
          Int.natCast_dvd_natCast.1 <| by rw [Int.ofNat_sub (le_of_lt b1)]; exact bm1.symm.dvd
        (yn_modEq_a_sub_one _ _).of_dvd this
      ⟨ky,
        Or.inr
          ⟨u, v, s, t, b, pell_eq _ _, pell_eq _ _, pell_eq _ _, b1, bm1, ba, vp, yv, sx, tk⟩⟩,
    fun ⟨a1, ky, o⟩ =>
    ⟨a1,
      match o with := by sorry
theorem eq_pow_of_pell_lem {a y k : ℕ} (hy0 : y ≠ 0) (hk0 : k ≠ 0) (hyk : y ^ k < a) :
    (↑(y ^ k) : ℤ) < 2 * a * y - y * y - 1 :=
  have hya : y < a := (Nat.le_self_pow hk0 _).trans_lt hyk
  calc
    (↑(y ^ k) : ℤ) < a := Nat.cast_lt.2 hyk
    _ ≤ (a : ℤ) ^ 2 - (a - 1 : ℤ) ^ 2 - 1 := by lia
    _ ≤ (a : ℤ) ^ 2 - (a - y : ℤ) ^ 2 - 1 := by sorry
theorem eq_pow_of_pell {m n k} :
    n ^ k = m ↔ k = 0 ∧ m = 1 ∨ 0 < k ∧ (n = 0 ∧ m = 0 ∨
      0 < n ∧ ∃ (w a t z : ℕ) (a1 : 1 < a), xn a1 k ≡ yn a1 k * (a - n) + m [MOD t] ∧
      2 * a * n = t + (n * n + 1) ∧ m < t ∧
      n ≤ w ∧ k ≤ w ∧ a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1) := by sorry
end Pell
