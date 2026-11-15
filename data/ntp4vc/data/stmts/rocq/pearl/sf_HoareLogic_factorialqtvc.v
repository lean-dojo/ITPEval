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
Inductive even : Z -> Prop :=
 | even_0 : even 0%Z
 | even_odd (x : Z) : even x -> even (x + 2%Z).
Axiom fact : Z -> Z.
Axiom fact_0 : fact 0%Z = 1%Z.
Axiom fact_n : forall  (n : Z) (fact0 : 0%Z < n), fact n = n * fact (n - 1%Z).
Theorem factorial'vc (x : Z) (fact0 : 0%Z ≤ x) : 0%Z ≤ x ∧ 1%Z * fact x = fact x ∧ (∀(z : Z) (y : Z), 0%Z ≤ z ∧ y * fact z = fact x -> (if decide (¬ z = 0%Z) then (0%Z ≤ z ∧ z - 1%Z < z) ∧ 0%Z ≤ z - 1%Z ∧ y * z * fact (z - 1%Z) = fact x else y = fact x)).
Admitted.
