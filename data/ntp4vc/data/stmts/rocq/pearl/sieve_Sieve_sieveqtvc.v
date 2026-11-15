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
Open Scope Z_scope.
Definition no_factor_lt (bnd : Z) (num : Z) := 1%Z < num ∧ (∀(k : Z) (l : Z), (1%Z < l ∧ l < bnd) ∧ 1%Z < k -> ¬ num = k * l).
Theorem sieve'vc (n : Z) (fact0 : 1%Z < n) : 0%Z ≤ n ∧ (∀(t : list bool), (∀(i : Z), 0%Z ≤ i ∧ i < n -> nth (Z.to_nat i) t inhabitant = true) ∧ Z.of_nat (length t) = n -> (let o1 : bool := false in (0%Z ≤ 0%Z ∧ 0%Z < Z.of_nat (length t)) ∧ (length (set_list t 0%nat o1) = length t -> nth_i (set_list t 0%nat o1) = fun_updt (nth_i t) 0%Z o1 -> (let o2 : bool := false in (0%Z ≤ 1%Z ∧ 1%Z < Z.of_nat (length (set_list t 0%nat o1))) ∧ (length (set_list (set_list t 0%nat o1) 1%nat o2) = length (set_list t 0%nat o1) -> nth_i (set_list (set_list t 0%nat o1) 1%nat o2) = fun_updt (nth_i (set_list t 0%nat o1)) 1%Z o2 -> ((1%Z < 2%Z ∧ 2%Z ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) (set_list (set_list t 0%nat o1) 1%nat o2) inhabitant = true) = no_factor_lt 2%Z j)) ∧ (∀(i : Z) (t1 : list bool), length t1 = length (set_list (set_list t 0%nat o1) 1%nat o2) -> (1%Z < i ∧ i ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) t1 inhabitant = true) = no_factor_lt i j) -> (if decide (i < n) then (0%Z ≤ i ∧ i < Z.of_nat (length t1)) ∧ (if decide (nth (Z.to_nat i) t1 inhabitant = true) then ((1%Z < i ∧ i ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) t1 inhabitant = true) = (no_factor_lt i j ∧ (∀(k : Z), 1%Z < k ∧ k < i -> ¬ j = k * i)))) ∧ (∀(r : Z) (t2 : list bool), length t2 = length t1 -> (1%Z < r ∧ r ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) t2 inhabitant = true) = (no_factor_lt i j ∧ (∀(k : Z), 1%Z < k ∧ k < r -> ¬ j = k * i))) -> (if decide (r * i < n) then let o3 : bool := false in (0%Z ≤ r * i ∧ r * i < Z.of_nat (length t2)) ∧ (length (set_list t2 (Z.to_nat (r * i)) o3) = length t2 -> nth_i (set_list t2 (Z.to_nat (r * i)) o3) = fun_updt (nth_i t2) (r * i) o3 -> (0%Z ≤ n - r ∧ n - (r + 1%Z) < n - r) ∧ ((1%Z < r + 1%Z ∧ r + 1%Z ≤ n) ∧ r * i + i = (r + 1%Z) * i) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) (set_list t2 (Z.to_nat (r * i)) o3) inhabitant = true) = (no_factor_lt i j ∧ (∀(k : Z), 1%Z < k ∧ k < r + 1%Z -> ¬ j = k * i)))) else (0%Z ≤ n - i ∧ n - (i + 1%Z) < n - i) ∧ (1%Z < i + 1%Z ∧ i + 1%Z ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) t2 inhabitant = true) = no_factor_lt (i + 1%Z) j))) else (0%Z ≤ n - i ∧ n - (i + 1%Z) < n - i) ∧ (1%Z < i + 1%Z ∧ i + 1%Z ≤ n) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < n -> (nth (Z.to_nat j) t1 inhabitant = true) = no_factor_lt (i + 1%Z) j)) else Z.of_nat (length t1) = n ∧ (∀(i1 : Z), 0%Z ≤ i1 ∧ i1 < n -> (nth (Z.to_nat i1) t1 inhabitant = true) = prime i1)))))))).
Admitted.
