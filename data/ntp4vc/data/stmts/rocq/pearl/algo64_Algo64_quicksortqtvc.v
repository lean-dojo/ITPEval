From Stdlib Require Import Strings.String.
From Stdlib Require Import String Ascii.
From Stdlib Require Arith.
From stdpp Require Import base.
From stdpp Require Import fin_maps.
From stdpp Require Import gmap.
From stdpp Require Import base gmultiset.
From Stdlib Require Classical.
From Stdlib Require Import ZArith.
From stdpp.bitvector Require Import definitions tactics.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Reals.Rbasic_fun.
From Stdlib Require Import Reals.Abstract.ConstructiveAbs.
From Stdlib Require Import Reals.Rdefinitions.
From stdpp Require Import list_relations.
From stdpp Require Import list_numbers.
From stdpp Require Import functions.
From Stdlib Require Import ClassicalEpsilon.
From stdpp Require Import base decidable.
From Stdlib Require Import ZArith.Zeuclid.
From Stdlib Require Import ZArith.Znumtheory.
From stdpp Require Import propset.
From Stdlib Require Import Reals.
Require Import Why3.Base.
Require Import Why3.why3.Ref.Ref.
Require Import Why3.map.MapEq.
Require Import Why3.map.MapExchange.
Require Import Why3.map.MapPermut.
Require Import Why3.array.IntArraySorted.
Open Scope Z_scope.
Definition qs_partition (t1 : list Z) (t2 : list Z) (m : Z) (n : Z) (i : Z) (j : Z) (x : Z) := permut_sub' t1 t2 (Z.to_nat m) (Z.to_nat (n + 1%Z)) ∧ (∀(k : Z), m ≤ k ∧ k ≤ j -> nth (Z.to_nat k) t2 inhabitant ≤ x) ∧ (∀(k : Z), j < k ∧ k < i -> nth (Z.to_nat k) t2 inhabitant = x) ∧ (∀(k : Z), i ≤ k ∧ k ≤ n -> x ≤ nth (Z.to_nat k) t2 inhabitant).
Theorem quicksort'vc (m : Z) (n : Z) (a : list Z) (fact0 : 0%Z ≤ m) (fact1 : m ≤ n) (fact2 : n < Z.of_nat (length a)) : if decide (m < n) then (0%Z ≤ m ∧ m < n ∧ n < Z.of_nat (length a)) ∧ (∀(j : Z) (i : Z) (a1 : list Z), length a1 = length a -> (m ≤ j ∧ j < i ∧ i ≤ n) ∧ permut_sub' a a1 (Z.to_nat m) (Z.to_nat (n + 1%Z)) ∧ (∀(r : Z), m ≤ r ∧ r ≤ j -> nth (Z.to_nat r) a1 inhabitant ≤ 42%Z) ∧ (∀(r : Z), j < r ∧ r < i -> nth (Z.to_nat r) a1 inhabitant = 42%Z) ∧ (∀(r : Z), i ≤ r ∧ r ≤ n -> 42%Z ≤ nth (Z.to_nat r) a1 inhabitant) -> ((0%Z ≤ n - m ∧ j - m < n - m) ∧ 0%Z ≤ m ∧ m ≤ j ∧ j < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> permut_sub' a1 a2 (Z.to_nat m) (Z.to_nat (j + 1%Z)) ∧ sorted_sub1 a2 m (j + 1%Z) -> ((0%Z ≤ n - m ∧ n - i < n - m) ∧ 0%Z ≤ i ∧ i ≤ n ∧ n < Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> permut_sub' a2 a3 (Z.to_nat i) (Z.to_nat (n + 1%Z)) ∧ sorted_sub1 a3 i (n + 1%Z) -> permut_sub' a a3 (Z.to_nat m) (Z.to_nat (n + 1%Z)) ∧ sorted_sub1 a3 m (n + 1%Z)))) else permut_sub' a a (Z.to_nat m) (Z.to_nat (n + 1%Z)) ∧ sorted_sub1 a m (n + 1%Z).
Admitted.
