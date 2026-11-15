/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SumOverResidueClass

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`NNReal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## Tags

p-series, Cauchy condensation test
-/

@[expose] public section

/-!
### Schlömilch's generalization of the Cauchy condensation test

In this section we prove the Schlömilch's generalization of the Cauchy condensation test:
for a strictly increasing `u : ℕ → ℕ` with ratio of successive differences bounded and an
antitone `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`, `∑ k, f k` converges if and only if
so does `∑ k, (u (k + 1) - u k) * f (u k)`. Instead of giving a monolithic proof, we split it
into a series of lemmas with explicit estimates of partial sums of each series in terms of the
partial sums of the other series.
-/

/--
A sequence `u` has the property that its ratio of successive differences is bounded
when there is a positive real number `C` such that, for all n ∈ ℕ,
(u (n + 2) - u (n + 1)) ≤ C * (u (n + 1) - u n)
-/
def SuccDiffBounded (C : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, u (n + 2) - u (n + 1) ≤ C • (u (n + 1) - u n)

namespace Finset

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {f : ℕ → M} {u : ℕ → ℕ}

theorem le_sum_schlomilch' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ Ico (u 0) (u n), f k) ≤ ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by sorry
theorem le_sum_condensed' (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ Ico 1 (2 ^ n), f k) ≤ ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by sorry
theorem le_sum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range (u n), f k) ≤
      ∑ k ∈ range (u 0), f k + ∑ k ∈ range n, (u (k + 1) - u k) • f (u k) := by sorry
theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (2 ^ n), f k) ≤ f 0 + ∑ k ∈ range n, 2 ^ k • f (2 ^ k) := by sorry
theorem sum_schlomilch_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : Monotone u) (n : ℕ) :
    (∑ k ∈ range n, (u (k + 1) - u k) • f (u (k + 1))) ≤ ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by sorry
theorem sum_condensed_le' (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range n, 2 ^ k • f (2 ^ (k + 1))) ≤ ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by sorry
theorem sum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) (n : ℕ) :
    ∑ k ∈ range (n + 1), (u (k + 1) - u k) • f (u k) ≤
    (u 1 - u 0) • f (u 0) + C • ∑ k ∈ Ico (u 0 + 1) (u n + 1), f k := by sorry
theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
    (∑ k ∈ range (n + 1), 2 ^ k • f (2 ^ k)) ≤ f 1 + 2 • ∑ k ∈ Ico 2 (2 ^ n + 1), f k := by sorry
end Finset

namespace ENNReal

open Filter Finset

variable {u : ℕ → ℕ} {f : ℕ → ℝ≥0∞}

open NNReal in
theorem le_tsum_schlomilch (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu : StrictMono u) :
    ∑' k, f k ≤ ∑ k ∈ range (u 0), f k + ∑' k : ℕ, (u (k + 1) - u k) * f (u k) := by sorry
theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    ∑' k, f k ≤ f 0 + ∑' k : ℕ, 2 ^ k * f (2 ^ k) := by sorry
theorem tsum_schlomilch_le {C : ℕ} (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (h_nonneg : ∀ n, 0 ≤ f n) (hu : Monotone u) (h_succ_diff : SuccDiffBounded C u) :
    ∑' k : ℕ, (u (k + 1) - u k) * f (u k) ≤ (u 1 - u 0) * f (u 0) + C * ∑' k, f k := by sorry
theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) :
    (∑' k : ℕ, 2 ^ k * f (2 ^ k)) ≤ f 1 + 2 * ∑' k, f k := by sorry
end ENNReal

namespace NNReal

open Finset

open ENNReal in
/-- for a series of `NNReal` version. -/
theorem summable_schlomilch_iff {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ≥0}
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m)
    (h_pos : ∀ n, 0 < u n) (hu_strict : StrictMono u)
    (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ≥0)) * f (u k)) ↔ Summable f := by sorry
open ENNReal in
theorem summable_condensed_iff {f : ℕ → ℝ≥0} (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ≥0) ^ k * f (2 ^ k)) ↔ Summable f := by sorry
end NNReal

open NNReal in
/-- for series of nonnegative real numbers. -/
theorem summable_schlomilch_iff_of_nonneg {C : ℕ} {u : ℕ → ℕ} {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (h_pos : ∀ n, 0 < u n)
    (hu_strict : StrictMono u) (hC_nonzero : C ≠ 0) (h_succ_diff : SuccDiffBounded C u) :
    (Summable fun k : ℕ => (u (k + 1) - (u k : ℝ)) * f (u k)) ↔ Summable f := by sorry
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
    (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by sorry
theorem summable_condensed_iff_of_eventually_nonneg {f : ℕ → ℝ} (h_nonneg : 0 ≤ᶠ[Filter.atTop] f)
    (h_mono : ∀ᶠ k in Filter.atTop, f (k + 1) ≤ f k) :
    (Summable fun k : ℕ => (2 : ℝ) ^ k * f (2 ^ k)) ↔ Summable f := by sorry
section p_series

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/

namespace Real

open Filter

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem summable_nat_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by sorry
theorem summable_nat_rpow {p : ℝ} : Summable (fun n => (n : ℝ) ^ p : ℕ → ℝ) ↔ p < -1 := by sorry
theorem summable_one_div_nat_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by sorry
theorem summable_nat_pow_inv {p : ℕ} :
    Summable (fun n => ((n : ℝ) ^ p)⁻¹ : ℕ → ℝ) ↔ 1 < p := by sorry
theorem summable_one_div_nat_pow {p : ℕ} :
    Summable (fun n => 1 / (n : ℝ) ^ p : ℕ → ℝ) ↔ 1 < p := by sorry
theorem summable_one_div_int_pow {p : ℕ} :
    (Summable fun n : ℤ ↦ 1 / (n : ℝ) ^ p) ↔ 1 < p := by sorry
theorem summable_abs_int_rpow {b : ℝ} (hb : 1 < b) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (-b) := by sorry
theorem not_summable_natCast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) := by sorry
theorem not_summable_one_div_natCast : ¬Summable (fun n => 1 / n : ℕ → ℝ) := by sorry
theorem tendsto_sum_range_one_div_nat_succ_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n, (1 / (i + 1) : ℝ)) atTop atTop := by sorry
end Real

namespace NNReal

@[simp]
theorem summable_rpow_inv {p : ℝ} :
    Summable (fun n => ((n : ℝ≥0) ^ p)⁻¹ : ℕ → ℝ≥0) ↔ 1 < p := by sorry
theorem summable_rpow {p : ℝ} : Summable (fun n => (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ p < -1 := by sorry
theorem summable_one_div_rpow {p : ℝ} :
    Summable (fun n => 1 / (n : ℝ≥0) ^ p : ℕ → ℝ≥0) ↔ 1 < p := by sorry
end NNReal

end p_series

section

open Finset

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem sum_Ioc_inv_sq_le_sub {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (∑ i ∈ Ioc k n, ((i : α) ^ 2)⁻¹) ≤ (k : α)⁻¹ - (n : α)⁻¹ := by sorry
theorem sum_Ioo_inv_sq_le (k n : ℕ) : (∑ i ∈ Ioo k n, (i ^ 2 : α)⁻¹) ≤ 2 / (k + 1) :=
  calc
    (∑ i ∈ Ioo k n, ((i : α) ^ 2)⁻¹) ≤ ∑ i ∈ Ioc k (max (k + 1) n), ((i : α) ^ 2)⁻¹ := by sorry
end

open Set Nat in
/-- The harmonic series restricted to a residue class is not summable. -/
lemma Real.not_summable_indicator_one_div_natCast {m : ℕ} (hm : m ≠ 0) (k : ZMod m) :
    ¬ Summable ({n : ℕ | (n : ZMod m) = k}.indicator fun n : ℕ ↦ (1 / n : ℝ)) := by sorry
section shifted

open Filter Asymptotics Topology

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
lemma Real.summable_one_div_nat_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℕ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by sorry
lemma Real.summable_one_div_int_add_rpow (a : ℝ) (s : ℝ) :
    Summable (fun n : ℤ ↦ 1 / |n + a| ^ s) ↔ 1 < s := by sorry
theorem summable_pow_div_add {α : Type*} (x : α) [RCLike α] (q k : ℕ) (hq : 1 < q) :
    Summable fun n : ℕ => ‖(x / (↑n + k) ^ q)‖ := by sorry
end shifted
