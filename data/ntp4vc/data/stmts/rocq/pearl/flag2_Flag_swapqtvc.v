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
Inductive color :=
  | Blue : color
  | White : color
  | Red : color.
Axiom color_inhabited : Inhabited color.
Global Existing Instance color_inhabited.
Axiom color_countable : Countable color.
Global Existing Instance color_countable.
Definition monochrome (a : Z -> color) (i : Z) (j : Z) (c : color) := ∀(k : Z), i ≤ k ∧ k < j -> a k = c.
Axiom nb_occ : (Z -> color) -> Z -> Z -> color -> Z.
Axiom nb_occ'def : forall  (j : Z) (i : Z) (a : Z -> color) (c : color), if decide (j ≤ i) then nb_occ a i j c = 0%Z else if decide (a (j - 1%Z) = c) then nb_occ a i j c = 1%Z + nb_occ a i (j - 1%Z) c else nb_occ a i j c = nb_occ a i (j - 1%Z) c.
Theorem swap'vc (i : Z) (a : list color) (j : Z) (fact0 : 0%Z ≤ i) (fact1 : i < Z.of_nat (length a)) (fact2 : 0%Z ≤ j) (fact3 : j < Z.of_nat (length a)) : 0%Z ≤ i ∧ i < Z.of_nat (length a) ∧ (let ai : color := nth (Z.to_nat i) a inhabitant in (0%Z ≤ j ∧ j < Z.of_nat (length a)) ∧ (let aj : color := nth (Z.to_nat j) a inhabitant in (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (length (set_list a (Z.to_nat i) aj) = length a -> nth_i (set_list a (Z.to_nat i) aj) = fun_updt (nth_i a) i aj -> (0%Z ≤ j ∧ j < Z.of_nat (length (set_list a (Z.to_nat i) aj))) ∧ (length (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai) = length (set_list a (Z.to_nat i) aj) -> nth_i (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai) = fun_updt (nth_i (set_list a (Z.to_nat i) aj)) j ai -> nth (Z.to_nat i) (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai) inhabitant = nth (Z.to_nat j) a inhabitant ∧ nth (Z.to_nat j) (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai) inhabitant = nth (Z.to_nat i) a inhabitant ∧ (∀(k : Z), ¬ k = i ∧ ¬ k = j -> nth (Z.to_nat k) (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai) inhabitant = nth (Z.to_nat k) a inhabitant) ∧ (∀(k1 : Z) (k2 : Z) (c : color), (k1 ≤ i ∧ i < k2) ∧ k1 ≤ j ∧ j < k2 -> nb_occ (nth_i (set_list (set_list a (Z.to_nat i) aj) (Z.to_nat j) ai)) k1 k2 c = nb_occ (nth_i a) k1 k2 c))))).
Admitted.
