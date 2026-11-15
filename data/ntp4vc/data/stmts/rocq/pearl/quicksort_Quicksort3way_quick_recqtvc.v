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
Definition qs_partition (a1 : list Z) (a2 : list Z) (l : Z) (ml : Z) (mr : Z) (r : Z) (v : Z) := permut_sub' a1 a2 (Z.to_nat l) (Z.to_nat r) ∧ (∀(j : Z), l ≤ j ∧ j < ml -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), ml ≤ j ∧ j < mr -> nth (Z.to_nat j) a2 inhabitant = v) ∧ (∀(j : Z), mr ≤ j ∧ j < r -> v < nth (Z.to_nat j) a2 inhabitant).
Theorem quick_rec'vc (l : Z) (r : Z) (a : list Z) (fact0 : 0%Z ≤ l) (fact1 : l ≤ r) (fact2 : r ≤ Z.of_nat (length a)) : if decide (l + 1%Z < r) then (0%Z ≤ l ∧ l < Z.of_nat (length a)) ∧ (let v : Z := nth (Z.to_nat l) a inhabitant in let o1 : Z := l + 1%Z in ((l ≤ l ∧ l < o1 ∧ o1 ≤ r ∧ r ≤ r) ∧ (∀(j : Z), l ≤ j ∧ j < l -> nth (Z.to_nat j) a inhabitant < v) ∧ (∀(j : Z), l ≤ j ∧ j < o1 -> nth (Z.to_nat j) a inhabitant = v) ∧ (∀(j : Z), r ≤ j ∧ j < r -> v < nth (Z.to_nat j) a inhabitant) ∧ permut_sub' a a (Z.to_nat l) (Z.to_nat r)) ∧ (∀(i : Z) (mr : Z) (ml : Z) (a1 : list Z), length a1 = length a -> (l ≤ ml ∧ ml < i ∧ i ≤ mr ∧ mr ≤ r) ∧ (∀(j : Z), l ≤ j ∧ j < ml -> nth (Z.to_nat j) a1 inhabitant < v) ∧ (∀(j : Z), ml ≤ j ∧ j < i -> nth (Z.to_nat j) a1 inhabitant = v) ∧ (∀(j : Z), mr ≤ j ∧ j < r -> v < nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat r) -> (if decide (i < mr) then (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (if decide (nth (Z.to_nat i) a1 inhabitant < v) then ((0%Z ≤ ml ∧ ml < Z.of_nat (length a1)) ∧ 0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> array_exchange a1 a2 ml i -> (0%Z ≤ mr - i ∧ mr - (i + 1%Z) < mr - i) ∧ (l ≤ ml + 1%Z ∧ ml + 1%Z < i + 1%Z ∧ i + 1%Z ≤ mr ∧ mr ≤ r) ∧ (∀(j : Z), l ≤ j ∧ j < ml + 1%Z -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), ml + 1%Z ≤ j ∧ j < i + 1%Z -> nth (Z.to_nat j) a2 inhabitant = v) ∧ (∀(j : Z), mr ≤ j ∧ j < r -> v < nth (Z.to_nat j) a2 inhabitant) ∧ permut_sub' a a2 (Z.to_nat l) (Z.to_nat r)) else (0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ (if decide (v < nth (Z.to_nat i) a1 inhabitant) then ((0%Z ≤ i ∧ i < Z.of_nat (length a1)) ∧ 0%Z ≤ mr - 1%Z ∧ mr - 1%Z < Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> array_exchange a1 a2 i (mr - 1%Z) -> (0%Z ≤ mr - i ∧ mr - 1%Z - i < mr - i) ∧ (l ≤ ml ∧ ml < i ∧ i ≤ mr - 1%Z ∧ mr - 1%Z ≤ r) ∧ (∀(j : Z), l ≤ j ∧ j < ml -> nth (Z.to_nat j) a2 inhabitant < v) ∧ (∀(j : Z), ml ≤ j ∧ j < i -> nth (Z.to_nat j) a2 inhabitant = v) ∧ (∀(j : Z), mr - 1%Z ≤ j ∧ j < r -> v < nth (Z.to_nat j) a2 inhabitant) ∧ permut_sub' a a2 (Z.to_nat l) (Z.to_nat r)) else (0%Z ≤ mr - i ∧ mr - (i + 1%Z) < mr - i) ∧ (l ≤ ml ∧ ml < i + 1%Z ∧ i + 1%Z ≤ mr ∧ mr ≤ r) ∧ (∀(j : Z), l ≤ j ∧ j < ml -> nth (Z.to_nat j) a1 inhabitant < v) ∧ (∀(j : Z), ml ≤ j ∧ j < i + 1%Z -> nth (Z.to_nat j) a1 inhabitant = v) ∧ (∀(j : Z), mr ≤ j ∧ j < r -> v < nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 (Z.to_nat l) (Z.to_nat r))) else ((0%Z ≤ r - l ∧ ml - l < r - l) ∧ 0%Z ≤ l ∧ l ≤ ml ∧ ml ≤ Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> sorted_sub1 a2 l ml ∧ permut_sub' a1 a2 (Z.to_nat l) (Z.to_nat ml) -> ((0%Z ≤ r - l ∧ r - mr < r - l) ∧ 0%Z ≤ mr ∧ mr ≤ r ∧ r ≤ Z.of_nat (length a2)) ∧ (∀(a3 : list Z), length a3 = length a2 -> sorted_sub1 a3 mr r ∧ permut_sub' a2 a3 (Z.to_nat mr) (Z.to_nat r) -> sorted_sub1 a3 l r ∧ permut_sub' a a3 (Z.to_nat l) (Z.to_nat r)))))) else sorted_sub1 a l r ∧ permut_sub' a a (Z.to_nat l) (Z.to_nat r).
Admitted.
