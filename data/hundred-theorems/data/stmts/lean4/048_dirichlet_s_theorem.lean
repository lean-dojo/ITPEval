/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Coprime
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

The main steps of the proof are as follows.
1. Define `ArithmeticFunction.vonMangoldt.residueClass a` for `a : ZMod q`, which is
   a function `ℕ → ℝ` taking the value zero when `(n : ZMod q) ≠ a` and `Λ n` else
   (where `Λ` is the von Mangoldt function `ArithmeticFunction.vonMangoldt`; we have
   `Λ (p^k) = log p` for prime powers and `Λ n = 0` otherwise.)
2. Show that this function can be written as a linear combination of functions
   of the form `χ * Λ` (pointwise product) with Dirichlet characters `χ` mod `q`.
   See `ArithmeticFunction.vonMangoldt.residueClass_eq`.
3. This implies that the L-series of `ArithmeticFunction.vonMangoldt.residueClass a`
   agrees (on `re s > 1`) with the corresponding linear combination of negative logarithmic
   derivatives of Dirichlet L-functions.
   See `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`.
4. Define an auxiliary function `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a` that is
   this linear combination of negative logarithmic derivatives of L-functions minus
   `(q.totient)⁻¹/(s-1)`, which cancels the pole at `s = 1`.
   See `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` for the statement
   that the auxiliary function agrees with the L-series of
   `ArithmeticFunction.vonMangoldt.residueClass` up to the term `(q.totient)⁻¹/(s-1)`.
5. Show that the auxiliary function is continuous on `re s ≥ 1`;
   see `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux`.
   This relies heavily on the non-vanishing of Dirichlet L-functions on the *closed*
   half-plane `re s ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), which
   in turn can only be stated since we know that the L-series of a Dirichlet character
   extends to an entire function (unless the character is trivial; then there is a
   simple pole at `s = 1`); see `DirichletCharacter.LFunction_eq_LSeries`
   (contributed by David Loeffler).
6. Show that the sum of `Λ n / n` over any residue class, but *excluding* the primes, converges.
   See `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.
7. Combining these ingredients, we can deduce that the sum of `Λ n / n` over
   the *primes* in a residue class must diverge.
   See `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`.
8. This finally easily implies that there must be infinitely many primes in the residue class.

## Definitions

* `ArithmeticFunction.vonMangoldt.residueClass a` (see above).
* `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` (see above).

## Main Result

We give two versions of **Dirichlet's Theorem**:
* `Nat.infinite_setOf_prime_and_eq_mod` states that the set of primes `p`
  such that `(p : ZMod q) = a` is infinite (when `a` is invertible in `ZMod q`).
* `Nat.forall_exists_prime_gt_and_eq_mod` states that for any natural number `n`
  there is a prime `p > n` such that `(p : ZMod q) = a`.

## Tags

prime number, arithmetic progression, residue class, Dirichlet's Theorem
-/

@[expose] public section

/-!
### Auxiliary statements

An infinite product or sum over a function supported in prime powers can be written
as an iterated product or sum over primes and natural numbers.
-/

section auxiliary

variable {α β γ : Type*} [CommGroup α] [UniformSpace α] [IsUniformGroup α] [CompleteSpace α]
  [T0Space α]

open Nat.Primes in
@[to_additive tsum_eq_tsum_primes_of_support_subset_prime_powers]
lemma tprod_eq_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 1)) := by sorry
lemma tprod_eq_tprod_primes_mul_tprod_primes_of_mulSupport_subset_prime_powers {f : ℕ → α}
    (hfm : Multipliable f) (hf : Function.mulSupport f ⊆ {n | IsPrimePow n}) :
    ∏' n : ℕ, f n = (∏' p : Nat.Primes, f p) * ∏' (p : Nat.Primes) (k : ℕ), f (p ^ (k + 2)) := by sorry
end auxiliary

/-!
### The L-series of the von Mangoldt function restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction.vonMangoldt

open Complex LSeries DirichletCharacter

open scoped LSeries.notation

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
  Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg

lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ vonMangoldt_nonneg)

@[simp]
lemma residueClass_apply_zero : residueClass a 0 = 0 := by sorry
lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) ≤ 1 := by sorry
lemma support_residueClass_prime_div :
    Function.support (fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n) =
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by sorry
open Nat.Primes

private lemma summable_F'' : Summable F'' := by sorry
lemma summable_residueClass_non_primes_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n := by sorry
variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by sorry
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by sorry
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by sorry
variable (a)

open Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`;
see `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`. -/
noncomputable
abbrev LFunctionResidueClassAux (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

/-- The auxiliary function is continuous away from the zeros of the L-functions of the Dirichlet
characters mod `q` (including at `s = 1`). -/
lemma continuousOn_LFunctionResidueClassAux' :
    ContinuousOn (LFunctionResidueClassAux a)
      {s | s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0} := by sorry
lemma continuousOn_LFunctionResidueClassAux :
    ContinuousOn (LFunctionResidueClassAux a) {s | 1 ≤ s.re} := by sorry
variable {a}

open scoped LSeries.notation

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
    Set.EqOn (LFunctionResidueClassAux a)
      (fun s ↦ L ↗(residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by sorry
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    LFunctionResidueClassAux a x = (LFunctionResidueClassAux a x).re := by sorry
variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹/(x-1) - C`. -/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, residueClass a n / (n : ℝ) ^ x := by sorry
open vonMangoldt Filter Topology in
/-- The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such primes. -/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n := by sorry
end ArithmeticFunction.vonMangoldt

end arith_prog

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem infinite_setOf_prime_and_eq_mod (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by sorry
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by sorry
theorem forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] := by sorry
theorem forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] := by sorry
open Filter in
lemma frequently_atTop_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] := by sorry
lemma infinite_setOf_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

end Nat

end DirichletsTheorem
