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
Axiom infix_sl : Z -> Z -> Z.
Axiom infix_sl'def : forall  (y : Z) (x : Z) (fact0 : ¬ y = 0%Z), infix_sl x y = ZEuclid.div x y.
Axiom comb : Z -> Z -> Z.
Axiom comb'def : forall  (k : Z) (n : Z) (fact0 : 0%Z ≤ k) (fact1 : k ≤ n), if decide (k = 0%Z ∨ k = n) then comb n k = 1%Z else comb n k = comb (n - 1%Z) k + comb (n - 1%Z) (k - 1%Z).
Axiom comb'spec : forall  (k : Z) (n : Z) (fact0 : 0%Z ≤ k) (fact1 : k ≤ n), 1%Z ≤ comb n k.
Theorem compute'vc (k : Z) (n : Z) (fact0 : 0%Z ≤ k) (fact1 : k ≤ n) : let k1 : Z := Z.min k (n - k) in (1%Z ≤ k1 + 1%Z -> ((1%Z ≤ 1%Z ∧ 1%Z ≤ k1 + 1%Z) ∧ 1%Z = comb n (1%Z - 1%Z)) ∧ (∀(r : Z), (∀(i : Z), (1%Z ≤ i ∧ i ≤ k1) ∧ (1%Z ≤ i ∧ i ≤ k1 + 1%Z) ∧ r = comb n (i - 1%Z) -> ¬ i = 0%Z ∧ (1%Z ≤ i + 1%Z ∧ i + 1%Z ≤ k1 + 1%Z) ∧ infix_sl (r * (n - i + 1%Z)) i = comb n (i + 1%Z - 1%Z)) ∧ ((1%Z ≤ k1 + 1%Z ∧ k1 + 1%Z ≤ k1 + 1%Z) ∧ r = comb n (k1 + 1%Z - 1%Z) -> r = comb n k))) ∧ (k1 + 1%Z < 1%Z -> 1%Z = comb n k).
Admitted.
