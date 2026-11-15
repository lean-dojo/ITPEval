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
Theorem update_aux'vc (t : tree) (a : list Z) (i : Z) (v : Z) (fact0 : is_tree_for t a (low (indexes1 t)) (high (indexes1 t))) (fact1 : low (indexes1 t) ≤ i) (fact2 : i < high (indexes1 t)) : (match t with | Leaf ind => True | Node ind l r => (if decide (i < high (indexes1 l)) then (match t with | Leaf _ => False | Node _ f f1 => f = l ∨ f1 = l end) ∧ is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) ∧ low (indexes1 l) ≤ i ∧ i < high (indexes1 l) else (match t with | Leaf _ => False | Node _ f f1 => f = r ∨ f1 = r end) ∧ is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) ∧ low (indexes1 r) ≤ i ∧ i < high (indexes1 r)) end) ∧ (∀(t' : tree) (delta : Z), (match t with | Leaf ind => t' = Leaf (indexes'mk (low ind) (high ind) v) ∧ delta = v - isum ind | Node ind l r => (if decide (i < high (indexes1 l)) then ∃(t'1 : tree), (low (indexes1 t'1) = low (indexes1 l) ∧ high (indexes1 t'1) = high (indexes1 l) ∧ is_tree_for t'1 (set_list a (Z.to_nat i) v) (low (indexes1 t'1)) (high (indexes1 t'1))) ∧ t' = Node (indexes'mk (low ind) (high ind) (isum ind + (v - nth (Z.to_nat i) a inhabitant))) t'1 r ∧ delta = v - nth (Z.to_nat i) a inhabitant else ∃(t'1 : tree), (low (indexes1 t'1) = low (indexes1 r) ∧ high (indexes1 t'1) = high (indexes1 r) ∧ is_tree_for t'1 (set_list a (Z.to_nat i) v) (low (indexes1 t'1)) (high (indexes1 t'1))) ∧ t' = Node (indexes'mk (low ind) (high ind) (isum ind + (v - nth (Z.to_nat i) a inhabitant))) l t'1 ∧ delta = v - nth (Z.to_nat i) a inhabitant) end) -> delta = v - nth (Z.to_nat i) a inhabitant ∧ low (indexes1 t') = low (indexes1 t) ∧ high (indexes1 t') = high (indexes1 t) ∧ is_tree_for t' (set_list a (Z.to_nat i) v) (low (indexes1 t')) (high (indexes1 t'))).
Admitted.
