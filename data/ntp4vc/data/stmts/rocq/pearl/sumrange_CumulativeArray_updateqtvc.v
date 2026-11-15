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
Require Import sumrange_vcg.sumrange.ArraySum.
Require Import sumrange_vcg.sumrange.ExtraLemmas.
Open Scope Z_scope.
Definition is_cumulative_array_for (c : list Z) (a : list Z) := Z.of_nat (length c) = Z.of_nat (length a) + 1%Z ∧ (∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length c) -> nth (Z.to_nat i) c inhabitant = sum a 0%Z i).
Theorem update'vc (c : list Z) (a : list Z) (i : Z) (v : Z) (fact0 : is_cumulative_array_for c a) (fact1 : 0%Z ≤ i) (fact2 : i < Z.of_nat (length a)) : 0%Z ≤ i ∧ i < Z.of_nat (length c) ∧ (let o1 : Z := i + 1%Z in (0%Z ≤ o1 ∧ o1 < Z.of_nat (length c)) ∧ (let incr : Z := v - nth (Z.to_nat o1) c inhabitant + nth (Z.to_nat i) c inhabitant in (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (length (set_list a (Z.to_nat i) v) = length a -> nth_i (set_list a (Z.to_nat i) v) = fun_updt (nth_i a) i v -> (let o2 : Z := Z.of_nat (length c) - 1%Z in let o3 : Z := i + 1%Z in (o3 ≤ o2 + 1%Z -> ((∀(k : Z), o3 ≤ k ∧ k < Z.of_nat (length c) -> nth (Z.to_nat k) c inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k - incr) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < o3 -> nth (Z.to_nat k) c inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k)) ∧ (∀(c1 : list Z), length c1 = length c -> (∀(j : Z), (o3 ≤ j ∧ j ≤ o2) ∧ (∀(k : Z), j ≤ k ∧ k < Z.of_nat (length c1) -> nth (Z.to_nat k) c1 inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k - incr) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < j -> nth (Z.to_nat k) c1 inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k) -> (0%Z ≤ j ∧ j < Z.of_nat (length c1)) ∧ (let o4 : Z := nth (Z.to_nat j) c1 inhabitant + incr in (0%Z ≤ j ∧ j < Z.of_nat (length c1)) ∧ (length (set_list c1 (Z.to_nat j) o4) = length c1 -> nth_i (set_list c1 (Z.to_nat j) o4) = fun_updt (nth_i c1) j o4 -> (∀(k : Z), j + 1%Z ≤ k ∧ k < Z.of_nat (length (set_list c1 (Z.to_nat j) o4)) -> nth (Z.to_nat k) (set_list c1 (Z.to_nat j) o4) inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k - incr) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < j + 1%Z -> nth (Z.to_nat k) (set_list c1 (Z.to_nat j) o4) inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k)))) ∧ ((∀(k : Z), o2 + 1%Z ≤ k ∧ k < Z.of_nat (length c1) -> nth (Z.to_nat k) c1 inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k - incr) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < o2 + 1%Z -> nth (Z.to_nat k) c1 inhabitant = sum (set_list a (Z.to_nat i) v) 0%Z k) -> is_cumulative_array_for c1 (set_list a (Z.to_nat i) v) ∧ nth (Z.to_nat i) (set_list a (Z.to_nat i) v) inhabitant = v ∧ (∀(k : Z), (0%Z ≤ k ∧ k < Z.of_nat (length (set_list a (Z.to_nat i) v))) ∧ ¬ k = i -> nth (Z.to_nat k) (set_list a (Z.to_nat i) v) inhabitant = nth (Z.to_nat k) a inhabitant)))) ∧ (o2 + 1%Z < o3 -> is_cumulative_array_for c (set_list a (Z.to_nat i) v) ∧ nth (Z.to_nat i) (set_list a (Z.to_nat i) v) inhabitant = v ∧ (∀(k : Z), (0%Z ≤ k ∧ k < Z.of_nat (length (set_list a (Z.to_nat i) v))) ∧ ¬ k = i -> nth (Z.to_nat k) (set_list a (Z.to_nat i) v) inhabitant = nth (Z.to_nat k) a inhabitant)))))).
Admitted.
