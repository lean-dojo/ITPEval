/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.List.Prime
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Subperm

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.primeFactorsList n`: the prime factorization of `n`
- `Nat.primeFactorsList_unique`: uniqueness of the prime factorisation

-/

@[expose] public section

assert_not_exists Multiset

open Bool Subtype

open Nat

namespace Nat

/-- `primeFactorsList n` is the prime factorization of `n`, listed in increasing order. -/
def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]
theorem primeFactorsList_zero : primeFactorsList 0 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_one : primeFactorsList 1 = [] := by rw [primeFactorsList]

@[simp]
theorem primeFactorsList_two : primeFactorsList 2 = [2] := by simp [primeFactorsList]

theorem prime_of_mem_primeFactorsList {n : ℕ} : ∀ {p : ℕ}, p ∈ primeFactorsList n → Prime p := by sorry
theorem pos_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ primeFactorsList n) : 0 < p :=
  Prime.pos (prime_of_mem_primeFactorsList h)

theorem prod_primeFactorsList : ∀ {n}, n ≠ 0 → List.prod (primeFactorsList n) = n := by sorry
theorem primeFactorsList_prime {p : ℕ} (hp : Nat.Prime p) : p.primeFactorsList = [p] := by sorry
theorem isChain_cons_primeFactorsList {n : ℕ} :
    ∀ {a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.IsChain (· ≤ ·) (a :: primeFactorsList n) := by sorry
theorem isChain_two_cons_primeFactorsList (n) : List.IsChain (· ≤ ·) (2 :: primeFactorsList n) :=
  isChain_cons_primeFactorsList fun _ pp _ => pp.two_le

theorem isChain_primeFactorsList (n) : List.IsChain (· ≤ ·) (primeFactorsList n) :=
  (isChain_two_cons_primeFactorsList _).tail

theorem primeFactorsList_sorted (n : ℕ) : List.SortedLE (primeFactorsList n) :=
  (isChain_primeFactorsList _).sortedLE

/-- `primeFactorsList` can be constructed inductively by extracting `minFac`, for sufficiently
large `n`. -/
theorem primeFactorsList_add_two (n : ℕ) :
    primeFactorsList (n + 2) = minFac (n + 2) :: primeFactorsList ((n + 2) / minFac (n + 2)) := by sorry
theorem primeFactorsList_eq_nil (n : ℕ) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 1 := by sorry
theorem primeFactorsList_ne_nil (n : ℕ) : n.primeFactorsList ≠ [] ↔ 1 < n := by sorry
open scoped List in
theorem eq_of_perm_primeFactorsList {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.primeFactorsList ~ b.primeFactorsList) : a = b := by sorry
open List

theorem mem_primeFactorsList_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    p ∈ primeFactorsList n ↔ p ∣ n where
  mp h := prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h ↦ prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)

theorem dvd_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ∣ n := by sorry
theorem mem_primeFactorsList {n p} (hn : n ≠ 0) : p ∈ primeFactorsList n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩

@[simp] lemma mem_primeFactorsList' {n p} : p ∈ n.primeFactorsList ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by sorry
theorem le_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ≤ n := by sorry
theorem primeFactorsList_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) :
    l ~ primeFactorsList n := by sorry
theorem Prime.primeFactorsList_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p ^ n).primeFactorsList = List.replicate n p := by sorry
theorem eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0)
    (h : ∀ {d}, Nat.Prime d → d ∣ n → d = p) : n = p ^ n.primeFactorsList.length := by sorry
theorem perm_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by sorry
theorem perm_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by sorry
theorem primeFactorsList_sublist_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList <+ (n * k).primeFactorsList := by sorry
theorem primeFactorsList_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList <+ k.primeFactorsList := by sorry
theorem primeFactorsList_subset_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList ⊆ (n * k).primeFactorsList :=
  (primeFactorsList_sublist_right h).subset

theorem primeFactorsList_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList ⊆ k.primeFactorsList :=
  (primeFactorsList_sublist_of_dvd h h').subset

theorem dvd_of_primeFactorsList_subperm {a b : ℕ} (ha : a ≠ 0)
    (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b := by sorry
theorem replicate_subperm_primeFactorsList_iff {a b n : ℕ} (ha : Prime a) (hb : b ≠ 0) :
    replicate n a <+~ primeFactorsList b ↔ a ^ n ∣ b := by sorry
end

theorem mem_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∨ p ∈ b.primeFactorsList := by sorry
theorem coprime_primeFactorsList_disjoint {a b : ℕ} (hab : a.Coprime b) :
    List.Disjoint a.primeFactorsList b.primeFactorsList := by sorry
theorem mem_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∪ b.primeFactorsList := by sorry
open List

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
theorem mem_primeFactorsList_mul_left {p a b : ℕ} (hpa : p ∈ a.primeFactorsList) (hb : b ≠ 0) :
    p ∈ (a * b).primeFactorsList := by sorry
theorem mem_primeFactorsList_mul_right {p a b : ℕ} (hpb : p ∈ b.primeFactorsList) (ha : a ≠ 0) :
    p ∈ (a * b).primeFactorsList := by sorry
theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
    (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩

theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : ℕ} (n2 : 2 < n) :
    4 ∣ n ∨ ∃ p, Prime p ∧ p ∣ n ∧ Odd p := by sorry
end Nat
