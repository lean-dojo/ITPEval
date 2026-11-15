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
Open Scope Z_scope.
Theorem binary_sort'vc (a : list Z) : let o1 : Z := Z.of_nat (length a) - 1%Z in (1%Z ≤ o1 + 1%Z -> ((∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < 1%Z -> nth (Z.to_nat i) a inhabitant ≤ nth (Z.to_nat j) a inhabitant) ∧ permut_sub' a a 0%nat (length a)) ∧ (∀(a1 : list Z), length a1 = length a -> (∀(k : Z), (1%Z ≤ k ∧ k ≤ o1) ∧ (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < k -> nth (Z.to_nat i) a1 inhabitant ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 0%nat (length a1) -> (0%Z ≤ k ∧ k < Z.of_nat (length a1)) ∧ (let v : Z := nth (Z.to_nat k) a1 inhabitant in ((0%Z ≤ 0%Z ∧ 0%Z ≤ k ∧ k ≤ k) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < 0%Z -> nth (Z.to_nat i) a1 inhabitant ≤ v) ∧ (∀(i : Z), k ≤ i ∧ i < k -> v < nth (Z.to_nat i) a1 inhabitant)) ∧ (∀(right1 : Z) (left1 : Z), (0%Z ≤ left1 ∧ left1 ≤ right1 ∧ right1 ≤ k) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < left1 -> nth (Z.to_nat i) a1 inhabitant ≤ v) ∧ (∀(i : Z), right1 ≤ i ∧ i < k -> v < nth (Z.to_nat i) a1 inhabitant) -> (if decide (left1 < right1) then ¬ 2%Z = 0%Z ∧ (let mid : Z := left1 + Z.rem (right1 - left1) 2%Z in (0%Z ≤ mid ∧ mid < Z.of_nat (length a1)) ∧ (if decide (v < nth (Z.to_nat mid) a1 inhabitant) then (0%Z ≤ right1 - left1 ∧ mid - left1 < right1 - left1) ∧ (0%Z ≤ left1 ∧ left1 ≤ mid ∧ mid ≤ k) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < left1 -> nth (Z.to_nat i) a1 inhabitant ≤ v) ∧ (∀(i : Z), mid ≤ i ∧ i < k -> v < nth (Z.to_nat i) a1 inhabitant) else (0%Z ≤ right1 - left1 ∧ right1 - (mid + 1%Z) < right1 - left1) ∧ (0%Z ≤ mid + 1%Z ∧ mid + 1%Z ≤ right1 ∧ right1 ≤ k) ∧ (∀(i : Z), 0%Z ≤ i ∧ i < mid + 1%Z -> nth (Z.to_nat i) a1 inhabitant ≤ v) ∧ (∀(i : Z), right1 ≤ i ∧ i < k -> v < nth (Z.to_nat i) a1 inhabitant))) else let o2 : Z := k - left1 in let o3 : Z := left1 + 1%Z in ((0%Z ≤ left1 ∧ 0%Z ≤ o2 ∧ left1 + o2 ≤ Z.of_nat (length a1)) ∧ 0%Z ≤ o3 ∧ o3 + o2 ≤ Z.of_nat (length a1)) ∧ (∀(a2 : list Z), length a2 = length a1 -> (∀(i : Z), 0%Z ≤ i ∧ i < o3 ∨ o3 + o2 ≤ i ∧ i < Z.of_nat (length a2) -> nth (Z.to_nat i) a2 inhabitant = nth (Z.to_nat i) a1 inhabitant) ∧ (∀(i : Z), o3 ≤ i ∧ i < o3 + o2 -> nth (Z.to_nat i) a2 inhabitant = nth (Z.to_nat (left1 + i - o3)) a1 inhabitant) -> (0%Z ≤ left1 ∧ left1 < Z.of_nat (length a2)) ∧ (length (set_list a2 (Z.to_nat left1) v) = length a2 -> nth_i (set_list a2 (Z.to_nat left1) v) = fun_updt (nth_i a2) left1 v -> (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < k + 1%Z -> nth (Z.to_nat i) (set_list a2 (Z.to_nat left1) v) inhabitant ≤ nth (Z.to_nat j) (set_list a2 (Z.to_nat left1) v) inhabitant) ∧ permut_sub' a (set_list a2 (Z.to_nat left1) v) 0%nat (length (set_list a2 (Z.to_nat left1) v)))))))) ∧ ((∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < o1 + 1%Z -> nth (Z.to_nat i) a1 inhabitant ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 0%nat (length a1) -> (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < Z.of_nat (length a1) -> nth (Z.to_nat i) a1 inhabitant ≤ nth (Z.to_nat j) a1 inhabitant) ∧ permut_sub' a a1 0%nat (length a1)))) ∧ (o1 + 1%Z < 1%Z -> (∀(i : Z) (j : Z), 0%Z ≤ i ∧ i ≤ j ∧ j < Z.of_nat (length a) -> nth (Z.to_nat i) a inhabitant ≤ nth (Z.to_nat j) a inhabitant) ∧ permut_sub' a a 0%nat (length a)).
Admitted.
