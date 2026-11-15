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
Theorem create'vc (a : list Z) : let l : Z := Z.of_nat (length a) in let o1 : Z := l + 1%Z in 0%Z ≤ o1 ∧ (∀(s : list Z), (∀(i : Z), 0%Z ≤ i ∧ i < o1 -> nth (Z.to_nat i) s inhabitant = 0%Z) ∧ Z.of_nat (length s) = o1 -> (1%Z ≤ l + 1%Z -> (∀(k : Z), 0%Z ≤ k ∧ k < 1%Z -> nth (Z.to_nat k) s inhabitant = sum a 0%Z k) ∧ (∀(s1 : list Z), length s1 = length s -> (∀(i : Z), (1%Z ≤ i ∧ i ≤ l) ∧ (∀(k : Z), 0%Z ≤ k ∧ k < i -> nth (Z.to_nat k) s1 inhabitant = sum a 0%Z k) -> (let o2 : Z := i - 1%Z in (0%Z ≤ o2 ∧ o2 < Z.of_nat (length a)) ∧ (let o3 : Z := i - 1%Z in (0%Z ≤ o3 ∧ o3 < Z.of_nat (length s1)) ∧ (let o4 : Z := nth (Z.to_nat o3) s1 inhabitant + nth (Z.to_nat o2) a inhabitant in (0%Z ≤ i ∧ i < Z.of_nat (length s1)) ∧ (length (set_list s1 (Z.to_nat i) o4) = length s1 -> nth_i (set_list s1 (Z.to_nat i) o4) = fun_updt (nth_i s1) i o4 -> (∀(k : Z), 0%Z ≤ k ∧ k < i + 1%Z -> nth (Z.to_nat k) (set_list s1 (Z.to_nat i) o4) inhabitant = sum a 0%Z k)))))) ∧ ((∀(k : Z), 0%Z ≤ k ∧ k < l + 1%Z -> nth (Z.to_nat k) s1 inhabitant = sum a 0%Z k) -> is_cumulative_array_for s1 a))) ∧ (l + 1%Z < 1%Z -> is_cumulative_array_for s a)).
Admitted.
