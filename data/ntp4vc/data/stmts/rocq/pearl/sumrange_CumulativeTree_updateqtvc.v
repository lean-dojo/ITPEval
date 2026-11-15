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
Inductive indexes :=
  | indexes'mk : Z -> Z -> Z -> indexes.
Axiom indexes_inhabited : Inhabited indexes.
Global Existing Instance indexes_inhabited.
Axiom indexes_countable : Countable indexes.
Global Existing Instance indexes_countable.
Definition low (x : indexes) := match x with |  indexes'mk a _ _ => a end.
Definition high (x : indexes) := match x with |  indexes'mk _ a _ => a end.
Definition isum (x : indexes) := match x with |  indexes'mk _ _ a => a end.
Inductive tree :=
  | Leaf : indexes -> tree
  | Node : indexes -> tree -> tree -> tree.
Axiom tree_inhabited : Inhabited tree.
Global Existing Instance tree_inhabited.
Axiom tree_countable : Countable tree.
Global Existing Instance tree_countable.
Definition indexes1 (t : tree) : indexes := match t with | Leaf ind => ind | Node ind _ _ => ind end.
Definition is_indexes_for (ind : indexes) (a : list Z) (i : Z) (j : Z) := low ind = i ∧ high ind = j ∧ (0%Z ≤ i ∧ i < j ∧ j ≤ Z.of_nat (length a)) ∧ isum ind = sum a i j.
Program Fixpoint is_tree_for (t : tree) (a : list Z) (i : Z) (j : Z) : Prop :=
match t with | Leaf ind => is_indexes_for ind a i j ∧ j = i + 1%Z | Node ind l r => is_indexes_for ind a i j ∧ i = low (indexes1 l) ∧ j = high (indexes1 r) ∧ (let m : Z := high (indexes1 l) in m = low (indexes1 r) ∧ (i < m ∧ m < j) ∧ m = Z.rem (i + j) 2%Z ∧ is_tree_for l a i m ∧ is_tree_for r a m j) end.
Admit Obligations.
Theorem update'vc (i : Z) (a : list Z) (t : tree) (v : Z) (fact0 : 0%Z ≤ i) (fact1 : i < Z.of_nat (length a)) (fact2 : is_tree_for t a 0%Z (Z.of_nat (length a))) : is_tree_for t a (low (indexes1 t)) (high (indexes1 t)) ∧ low (indexes1 t) ≤ i ∧ i < high (indexes1 t) ∧ (∀(t1 : tree), low (indexes1 t1) = low (indexes1 t) ∧ high (indexes1 t1) = high (indexes1 t) ∧ is_tree_for t1 (set_list a (Z.to_nat i) v) (low (indexes1 t1)) (high (indexes1 t1)) -> (0%Z ≤ i ∧ i < Z.of_nat (length a)) ∧ (length (set_list a (Z.to_nat i) v) = length a -> nth_i (set_list a (Z.to_nat i) v) = fun_updt (nth_i a) i v -> nth (Z.to_nat i) (set_list a (Z.to_nat i) v) inhabitant = v ∧ (∀(k : Z), (0%Z ≤ k ∧ k < Z.of_nat (length (set_list a (Z.to_nat i) v))) ∧ ¬ k = i -> nth (Z.to_nat k) (set_list a (Z.to_nat i) v) inhabitant = nth (Z.to_nat k) a inhabitant) ∧ is_tree_for t1 (set_list a (Z.to_nat i) v) 0%Z (Z.of_nat (length (set_list a (Z.to_nat i) v))))).
Admitted.
