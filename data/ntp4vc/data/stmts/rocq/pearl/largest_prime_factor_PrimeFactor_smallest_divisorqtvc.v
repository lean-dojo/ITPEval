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
Theorem smallest_divisor'vc (n : Z) (d : Z) (fact0 : 2%Z ≤ n) (fact1 : 2%Z ≤ d) (fact2 : d ≤ n) (fact3 : ∀(i : Z), 2%Z ≤ i ∧ i < d -> ¬ (i | n)) : let o1 : Z := d * d in (¬ n < o1 -> (2%Z ≤ d -> ¬ d = 0%Z) ∧ (∀(o2 : bool), (if decide (2%Z ≤ d) then o2 = (if decide (Z.quot n d = 0%Z) then true else false) else o2 = false) -> ¬ o2 = true -> (let o3 : Z := d + 1%Z in (0%Z ≤ n - d ∧ n - o3 < n - d) ∧ 2%Z ≤ n ∧ (2%Z ≤ o3 ∧ o3 ≤ n) ∧ (∀(i : Z), 2%Z ≤ i ∧ i < o3 -> ¬ (i | n))))) ∧ (∀(result : Z), (if decide (n < o1) then result = n else ∃(o2 : bool), (if decide (2%Z ≤ d) then o2 = (if decide (Z.quot n d = 0%Z) then true else false) else o2 = false) ∧ (if decide (o2 = true) then result = d else (d + 1%Z ≤ result ∧ result ≤ n) ∧ (result | n) ∧ (∀(i : Z), 2%Z ≤ i ∧ i < result -> ¬ (i | n)))) -> (d ≤ result ∧ result ≤ n) ∧ (result | n) ∧ (∀(i : Z), 2%Z ≤ i ∧ i < result -> ¬ (i | n))).
Admitted.
