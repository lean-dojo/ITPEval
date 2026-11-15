/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Glaisher's theorem

This file proves Glaisher's theorem: the number of partitions of an integer $n$ into parts not
divisible by $d$ is equal to the number of partitions in which no part is repeated $d$ or more
times.

## Main declarations
* `Nat.Partition.card_restricted_eq_card_countRestricted`: Glaisher's theorem.
* `Nat.Partition.card_odds_eq_card_distincts`: Euler's partition theorem, a special case
  of Glaisher's theorem when `m = 2`. This is also Theorem 45 from the
  [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

## Proof outline

The proof is based on the generating functions for `restricted` and `countRestricted` partitions,
which turn out to be equal:

$$\prod_{i=1,i\nmid m}^\infty\frac{1}{1-X^i}=\prod_{i=0}^\infty (1+X^{i+1}+\cdots+X^{(m-1)(i+1)})$$

## References
https://en.wikipedia.org/wiki/Glaisher%27s_theorem
-/

public section

variable (R) [TopologicalSpace R] [T2Space R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

section Semiring
variable [CommSemiring R]

/-- The generating function of `Nat.Partition.restricted n p` is
$$
\prod_{i \in p} \sum_{j = 0}^{\infty} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun i ↦ if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n ↦ (#(restricted n p) : R)) := by sorry
theorem multipliable_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    Multipliable (fun i ↦ if p (i + 1) then ∑' j : ℕ, (X ^ ((i + 1) * j) : R⟦X⟧) else 1) :=
  (hasProd_powerSeriesMk_card_restricted R p).multipliable

theorem powerSeriesMk_card_restricted_eq_tprod [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    PowerSeries.mk (fun n ↦ (#(restricted n p) : R)) =
    ∏' i, if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1 :=
  (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

/-- The generating function of `Nat.Partition.countRestricted n m` is
$$
\prod_{i = 1}^{\infty} \sum_{j = 0}^{m - 1} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    HasProd (fun i ↦ ∑ j ∈ range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (#(countRestricted n m) : R)) := by sorry
theorem multipliable_powerSeriesMk_card_countRestricted (m : ℕ) :
    Multipliable fun i ↦ ∑ j ∈ range m, (X ^ ((i + 1) * j) : R⟦X⟧) := by sorry
theorem powerSeriesMk_card_countRestricted_eq_tprod {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : R)) =
    ∏' i, ∑ j ∈ range m, X ^ ((i + 1) * j) :=
  (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

end Semiring

section Ring
variable [CommRing R] [NoZeroDivisors R]

private theorem aux_mul_one_sub_X_pow [IsTopologicalRing R] {m : ℕ} (hm : 0 < m) :
    (∏' i, if ¬m ∣ i + 1 then ∑' j, (X : R⟦X⟧) ^ ((i + 1) * j) else 1) * ∏' i, (1 - X ^ (i + 1)) =
    ∏' i, (1 - X ^ ((i + 1) * m)) := by sorry
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    (PowerSeries.mk fun n ↦ (#(restricted n (¬ m ∣ ·)) : R)) =
    PowerSeries.mk fun n ↦ (#(countRestricted n m) : R) := by sorry
end Ring

theorem card_restricted_eq_card_countRestricted (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by sorry
theorem card_odds_eq_card_distincts (n : ℕ) : #(odds n) = #(distincts n) := by sorry
end Nat.Partition
