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
Require Import Why3.int.Iter.
Require Import Why3.pigeon.Pigeonhole.
Open Scope Z_scope.
Axiom f : Z -> Z.
Axiom m : Z.
Axiom m_positive : 0%Z < m.
Axiom f_range : forall  (x : Z) (fact0 : 0%Z ≤ x) (fact1 : x < m), 0%Z ≤ f x ∧ f x < m.
Axiom x0 : Z.
Axiom x0'def : 0%Z ≤ x0 ∧ x0 < m.
Axiom f_closure : Z -> Z.
Axiom f_closure_def : forall  (y : Z), f_closure y = f y.
Definition x (i : Z) : Z := iter f_closure i x0.
Theorem tortoise_and_hare'vc (mu : Z) (lambda : Z) (fact0 : 0%Z ≤ mu) (fact1 : mu < m) (fact2 : 1%Z ≤ lambda) (fact3 : lambda ≤ m) (fact4 : mu + lambda ≤ m) (fact5 : x (mu + lambda) = x mu) (fact6 : ∀(i : Z) (j : Z), 0%Z ≤ i ∧ i < j ∧ j < mu + lambda -> ¬ x i = x j) : 1%Z ≤ 1%Z ∧ 1%Z ≤ mu + lambda ∧ f x0 = x 1%Z ∧ f (f x0) = x (2%Z * 1%Z) ∧ (∀(i : Z), 1%Z ≤ i ∧ i < 1%Z -> ¬ x i = x (2%Z * i)) ∧ (∀(n : Z), (1%Z ≤ n ∧ n ≤ mu + lambda) ∧ (∀(i : Z), 1%Z ≤ i ∧ i < n -> ¬ x i = x (2%Z * i)) -> (if decide (¬ x n = x (2%Z * n)) then ¬ mu + lambda < n + 1%Z ∧ (¬ mu + lambda < n + 1%Z -> (0%Z ≤ mu + lambda - n ∧ mu + lambda - (n + 1%Z) < mu + lambda - n) ∧ (1%Z ≤ n + 1%Z ∧ n + 1%Z ≤ mu + lambda) ∧ f (x n) = x (n + 1%Z) ∧ f (f (x (2%Z * n))) = x (2%Z * (n + 1%Z)) ∧ (∀(i : Z), 1%Z ≤ i ∧ i < n + 1%Z -> ¬ x i = x (2%Z * i))) else ((0%Z ≤ 0%Z ∧ 0%Z ≤ mu) ∧ (x0 = x 0%Z ∧ x n = x (n + 0%Z)) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < 0%Z -> ¬ x j = x (n + j)) ∧ (∀(j : Z), 0%Z < j ∧ j < 0%Z -> ¬ x (n + j) = x n)) ∧ (∀(lam : Z) (i : Z), (0%Z ≤ i ∧ i ≤ mu) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i -> ¬ x j = x (n + j)) ∧ (if decide (lam = 0%Z) then ∀(j : Z), 0%Z < j ∧ j < i -> ¬ x (n + j) = x n else lam = lambda) -> (if decide (¬ x i = x (n + i)) then ∀(o1 : bool), (if decide (lam = 0%Z) then o1 = (if decide (0%Z < i) then if decide (x (n + i) = x n) then true else false else false) else o1 = false) -> (if decide (o1 = true) then (0%Z ≤ mu - i ∧ mu - (i + 1%Z) < mu - i) ∧ (0%Z ≤ i + 1%Z ∧ i + 1%Z ≤ mu) ∧ (f (x i) = x (i + 1%Z) ∧ f (x (n + i)) = x (n + (i + 1%Z))) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i + 1%Z -> ¬ x j = x (n + j)) ∧ (if decide (i = 0%Z) then ∀(j : Z), 0%Z < j ∧ j < i + 1%Z -> ¬ x (n + j) = x n else i = lambda) else (0%Z ≤ mu - i ∧ mu - (i + 1%Z) < mu - i) ∧ (0%Z ≤ i + 1%Z ∧ i + 1%Z ≤ mu) ∧ (f (x i) = x (i + 1%Z) ∧ f (x (n + i)) = x (n + (i + 1%Z))) ∧ (∀(j : Z), 0%Z ≤ j ∧ j < i + 1%Z -> ¬ x j = x (n + j)) ∧ (if decide (lam = 0%Z) then ∀(j : Z), 0%Z < j ∧ j < i + 1%Z -> ¬ x (n + j) = x n else lam = lambda)) else ∀(l : Z), (if decide (lam = 0%Z) then l = n else l = lam) -> ((0%Z ≤ i ∧ i < m) ∧ (1%Z ≤ l ∧ l ≤ m) ∧ i + l ≤ m ∧ x (i + l) = x i) ∧ (∀(i1 : Z) (j : Z), 0%Z ≤ i1 ∧ i1 < j ∧ j < i + l -> ¬ x i1 = x j))))).
Admitted.
