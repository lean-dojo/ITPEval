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
Require Import sumrange_vcg.sumrange.ArraySum.
Open Scope Z_scope.
Theorem query'vc (i : Z) (j : Z) (a : list Z) (fact0 : 0%Z ≤ i) (fact1 : i ≤ j) (fact2 : j ≤ Z.of_nat (length a)) : let o1 : Z := j - 1%Z in (i ≤ o1 + 1%Z -> 0%Z = sum a i i ∧ (∀(s : Z), (∀(k : Z), (i ≤ k ∧ k ≤ o1) ∧ s = sum a i k -> (0%Z ≤ k ∧ k < Z.of_nat (length a)) ∧ s + nth (Z.to_nat k) a inhabitant = sum a i (k + 1%Z)) ∧ (s = sum a i (o1 + 1%Z) -> s = sum a i j))) ∧ (o1 + 1%Z < i -> 0%Z = sum a i j).
Admitted.
