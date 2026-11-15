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
Theorem parity'vc (x : Z) (fact0 : 0%Z ≤ x) : 0%Z ≤ x ∧ (even (x - x) ∨ 0%Z = 1%Z ∧ even (x - x + 1%Z)) ∧ (∀(y : Z) (x1 : Z), 0%Z ≤ x1 ∧ (y = 0%Z ∧ even (x - x1) ∨ y = 1%Z ∧ even (x - x1 + 1%Z)) -> (if decide (¬ x1 = 0%Z) then (0%Z ≤ x1 ∧ x1 - 1%Z < x1) ∧ 0%Z ≤ x1 - 1%Z ∧ (1%Z - y = 0%Z ∧ even (x - (x1 - 1%Z)) ∨ 1%Z - y = 1%Z ∧ even (x - (x1 - 1%Z) + 1%Z)) else (y = 0%Z) = even x)).
Admitted.
