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
Definition qs_partition (a1 : list Z) (a2 : list Z) (l : Z) (m : Z) (r : Z) (v : Z) := permut_sub' a1 a2 (Z.to_nat l) (Z.to_nat r) ∧ (∀(j : Z), l ≤ j ∧ j < m -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), m < j ∧ j < r -> v ≤ nth (Z.to_nat j) a2 inhabitant) ∧ nth (Z.to_nat m) a2 inhabitant = v.
Theorem quick_rec'vc (l : Z) (r : Z) (a : list Z) (fact0 : 0%Z ≤ l) (fact1 : l ≤ r) (fact2 : r ≤ Z.of_nat (length a)) : if decide (l + 1%Z < r) then (0%Z ≤ l ∧ l < Z.of_nat (length a)) ∧ (let v : Z := nth (Z.to_nat l) a inhabitant in let o1 : Z := r - 1%Z in let o2 : Z := l + 1%Z in (o2 ≤ o1 + 1%Z -> ((nth (Z.to_nat l) a inhabitant = v ∧ l ≤ l ∧ l < o2) ∧ (∀(j : Z), l < j ∧ j ≤ l -> nth (Z.to_nat j) a inhabitant < v) ∧ (∀(j : Z), l < j ∧ j < o2 -> v ≤ nth (Z.to_nat j) a inhabitant) ∧ permut_sub' a a (Z.to_nat l) (Z.to_nat r)) ∧ (∀(m : Z) (a1 : list Z), length a1 = length a -> (∀(i : Z), (o2 ≤ i ∧ i ≤ o1) ∧ (nth (Z.to_nat l) a1 inhabitant = v ∧ l ≤ m ∧ m < i) ∧ (∀(j : Z), l < j ∧ j ≤ m -> nth (Z.to_nat j) a1 inhabitant < v) ∧ (∀(j : Z), m < j ∧ j < i -> v ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat r) -> (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (if decide (nth (Z.to_nat i) a1 inhabitant < v) then ((0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ 0%Z ≤ m + 1%Z ∧ m + 1%Z < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> array_exchange a1 a2 i (m + 1%Z) -> (nth (Z.to_nat l) a2 inhabitant = v ∧ l ≤ m + 1%Z ∧ m + 1%Z < i + 1%Z) ∧ (∀(j : Z), l < j ∧ j ≤ m + 1%Z -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), m + 1%Z < j ∧ j < i + 1%Z -> v ≤ nth (Z.to_nat j) a2 inhabitant) ∧ permut_sub' a a2 (Z.to_nat l) (Z.to_nat r)) else (nth (Z.to_nat l) a1 inhabitant = v ∧ l ≤ m ∧ m < i + 1%Z) ∧ (∀(j : Z), l < j ∧ j ≤ m -> nth (Z.to_nat j) a1 inhabitant < v) ∧ (∀(j : Z), m < j ∧ j < i + 1%Z -> v ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat r))) ∧ ((nth (Z.to_nat l) a1 inhabitant = v ∧ l ≤ m ∧ m < o1 + 1%Z) ∧ (∀(j : Z), l < j ∧ j ≤ m -> nth (Z.to_nat j) a1 inhabitant < v) ∧ (∀(j : Z), m < j ∧ j < o1 + 1%Z -> v ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat r) -> ((0%Z ≤ l ∧ l < Z.of_nat (length a1)) ∧ 0%Z ≤ m ∧ m < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> array_exchange a1 a2 l m -> ((0%Z ≤ r - l ∧ m - l < r - l) ∧ 0%Z ≤ l ∧ l ≤ m ∧ m ≤ Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> sorted_sub1 a3 l m ∧ permut_sub' a2 a3 (Z.to_nat l) (Z.to_nat m) -> (let o3 : Z := m + 1%Z in ((0%Z ≤ r - l ∧ r - o3 < r - l) ∧ 0%Z ≤ o3 ∧ o3 ≤ r ∧ r ≤ Z.of_nat (length a3)) ∧ (∀(a4 : list Z), length a4 = length a3 -> sorted_sub1 a4 o3 r ∧ permut_sub' a3 a4 (Z.to_nat o3) (Z.to_nat r) -> sorted_sub1 a4 l r ∧ permut_sub' a a4 (Z.to_nat l) (Z.to_nat r)))))))) ∧ (o1 + 1%Z < o2 -> (0%Z ≤ l ∧ l < Z.of_nat (length a)) ∧ (∀(a1 : list Z), length a1 = length a -> array_exchange a a1 l l -> ((0%Z ≤ r - l ∧ l - l < r - l) ∧ 0%Z ≤ l ∧ l ≤ l ∧ l ≤ Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> sorted_sub1 a2 l l ∧ permut_sub' a1 a2 (Z.to_nat l) (Z.to_nat l) -> (let o3 : Z := l + 1%Z in ((0%Z ≤ r - l ∧ r - o3 < r - l) ∧ 0%Z ≤ o3 ∧ o3 ≤ r ∧ r ≤ Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> sorted_sub1 a3 o3 r ∧ permut_sub' a2 a3 (Z.to_nat o3) (Z.to_nat r) -> sorted_sub1 a3 l r ∧ permut_sub' a a3 (Z.to_nat l) (Z.to_nat r))))))) else sorted_sub1 a l r ∧ permut_sub' a a (Z.to_nat l) (Z.to_nat r).
Admitted.
