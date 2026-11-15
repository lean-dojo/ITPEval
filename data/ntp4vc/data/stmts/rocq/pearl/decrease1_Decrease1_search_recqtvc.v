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
Definition decrease1 (a : list Z) := ∀(i : Z), 0%Z ≤ i ∧ i < Z.of_nat (length a) - 1%Z -> nth (Z.to_nat i) a inhabitant - 1%Z ≤ nth (Z.to_nat (i + 1%Z)) a inhabitant.
Theorem search_rec'vc (a : list Z) (i : Z) (fact0 : decrease1 a) (fact1 : 0%Z ≤ i) : let o1 : Z := Z.of_nat (length a) in (i < o1 -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (¬ nth (Z.to_nat i) a inhabitant = 0%Z -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (if decide (0%Z < nth (Z.to_nat i) a inhabitant) then (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (let o2 : Z := i + nth (Z.to_nat i) a inhabitant in (0%Z ≤ Z.of_nat (length a) - i ∧ Z.of_nat (length a) - o2 < Z.of_nat (length a) - i) ∧ decrease1 a ∧ 0%Z ≤ o2) else let o2 : Z := i + 1%Z in (0%Z ≤ Z.of_nat (length a) - i ∧ Z.of_nat (length a) - o2 < Z.of_nat (length a) - i) ∧ decrease1 a ∧ 0%Z ≤ o2))) ∧ (∀(result : Z), (if decide (i < o1) then if decide (nth (Z.to_nat i) a inhabitant = 0%Z) then result = i else if decide (0%Z < nth (Z.to_nat i) a inhabitant) then let o2 : Z := i + nth (Z.to_nat i) a inhabitant in result = - 1%Z ∧ (∀(j : Z), o2 ≤ j ∧ j < Z.of_nat (length a) -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z) ∨ (o2 ≤ result ∧ result < Z.of_nat (length a)) ∧ nth (Z.to_nat result) a inhabitant = 0%Z ∧ (∀(j : Z), o2 ≤ j ∧ j < result -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z) else let o2 : Z := i + 1%Z in result = - 1%Z ∧ (∀(j : Z), o2 ≤ j ∧ j < Z.of_nat (length a) -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z) ∨ (o2 ≤ result ∧ result < Z.of_nat (length a)) ∧ nth (Z.to_nat result) a inhabitant = 0%Z ∧ (∀(j : Z), o2 ≤ j ∧ j < result -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z) else result = - 1%Z) -> result = - 1%Z ∧ (∀(j : Z), i ≤ j ∧ j < Z.of_nat (length a) -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z) ∨ (i ≤ result ∧ result < Z.of_nat (length a)) ∧ nth (Z.to_nat result) a inhabitant = 0%Z ∧ (∀(j : Z), i ≤ j ∧ j < result -> ¬ nth (Z.to_nat j) a inhabitant = 0%Z)).
Admitted.
