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
Theorem binary_gcd'vc (u : Z) (v : Z) (fact0 : 0%Z ≤ u) (fact1 : 0%Z ≤ v) : (if decide (u < v) then (0%Z ≤ v ∧ u < v ∨ v = u ∧ 0%Z ≤ u ∧ v < u) ∧ 0%Z ≤ v ∧ 0%Z ≤ u else ¬ v = 0%Z -> ¬ 2%Z = 0%Z ∧ (if decide (Z.quot u 2%Z = 0%Z) then ¬ 2%Z = 0%Z ∧ (if decide (Z.quot v 2%Z = 0%Z) then ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem v 2%Z in ¬ 2%Z = 0%Z ∧ (let o2 : Z := Z.rem u 2%Z in (0%Z ≤ v ∧ o1 < v ∨ v = o1 ∧ 0%Z ≤ u ∧ o2 < u) ∧ 0%Z ≤ o2 ∧ 0%Z ≤ o1)) else ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem u 2%Z in (0%Z ≤ u ∧ o1 < u) ∧ 0%Z ≤ o1 ∧ 0%Z ≤ v)) else ¬ 2%Z = 0%Z ∧ (if decide (Z.quot v 2%Z = 0%Z) then ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem v 2%Z in (0%Z ≤ v ∧ o1 < v) ∧ 0%Z ≤ u ∧ 0%Z ≤ o1) else ¬ 2%Z = 0%Z ∧ (let o1 : Z := Z.rem (u - v) 2%Z in (0%Z ≤ u ∧ o1 < u) ∧ 0%Z ≤ o1 ∧ 0%Z ≤ v)))) ∧ (∀(result : Z), (if decide (u < v) then result = Z.gcd v u else if decide (v = 0%Z) then result = u else if decide (Z.quot u 2%Z = 0%Z) then if decide (Z.quot v 2%Z = 0%Z) then result = 2%Z * Z.gcd (Z.rem u 2%Z) (Z.rem v 2%Z) else result = Z.gcd (Z.rem u 2%Z) v else if decide (Z.quot v 2%Z = 0%Z) then result = Z.gcd u (Z.rem v 2%Z) else result = Z.gcd (Z.rem (u - v) 2%Z) v) -> result = Z.gcd u v).
Admitted.
