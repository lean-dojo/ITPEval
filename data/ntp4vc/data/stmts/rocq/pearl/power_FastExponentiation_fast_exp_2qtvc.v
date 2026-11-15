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
Open Scope Z_scope.
Theorem fast_exp_2'vc (n : Z) (acc : Z) (x : Z) (fact0 : 0%Z ≤ n) : (¬ n = 0%Z -> ¬ 2%Z = 0%Z ∧ (if decide (Z.quot n 2%Z = 0%Z) then ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem n 2%Z in (0%Z ≤ n ∧ o1 < n) ∧ 0%Z ≤ o1) else let o1 : Z := n - 1%Z in (0%Z ≤ n ∧ o1 < n) ∧ 0%Z ≤ o1)) ∧ (∀(result : Z), (if decide (n = 0%Z) then result = acc else if decide (Z.quot n 2%Z = 0%Z) then result = Z.pow (x * x) (Z.rem n 2%Z) * acc else result = Z.pow x (n - 1%Z) * (x * acc)) -> result = Z.pow x n * acc).
Admitted.
