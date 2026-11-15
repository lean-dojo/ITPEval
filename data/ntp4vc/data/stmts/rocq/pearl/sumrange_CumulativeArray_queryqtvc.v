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
Theorem query'vc (c : list Z) (a : list Z) (i : Z) (j : Z) (fact0 : is_cumulative_array_for c a) (fact1 : 0%Z ≤ i) (fact2 : i ≤ j) (fact3 : j < Z.of_nat (length c)) : 0%Z ≤ i ∧ i < Z.of_nat (length c) ∧ 0%Z ≤ j ∧ j < Z.of_nat (length c) ∧ nth (Z.to_nat j) c inhabitant - nth (Z.to_nat i) c inhabitant = sum a i j.
Admitted.
