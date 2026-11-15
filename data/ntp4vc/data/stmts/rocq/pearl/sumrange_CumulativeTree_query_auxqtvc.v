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
Theorem query_aux'vc (t : tree) (a : list Z) (i : Z) (j : Z) (fact0 : is_tree_for t a (low (indexes1 t)) (high (indexes1 t))) (fact1 : 0%Z ≤ low (indexes1 t)) (fact2 : low (indexes1 t) ≤ i) (fact3 : i < j) (fact4 : j ≤ high (indexes1 t)) (fact5 : high (indexes1 t) ≤ Z.of_nat (length a)) : (match t with | Leaf ind => True | Node ind l r => (∀(o1 : bool), (if decide (i = low ind) then o1 = (if decide (j = high ind) then true else false) else o1 = false) -> ¬ o1 = true -> (let m : Z := high (indexes1 l) in if decide (j ≤ m) then (match t with | Leaf _ => False | Node _ f f1 => f = l ∨ f1 = l end) ∧ is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) ∧ 0%Z ≤ low (indexes1 l) ∧ low (indexes1 l) ≤ i ∧ i < j ∧ j ≤ high (indexes1 l) ∧ high (indexes1 l) ≤ Z.of_nat (length a) else if decide (m ≤ i) then (match t with | Leaf _ => False | Node _ f f1 => f = r ∨ f1 = r end) ∧ is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) ∧ 0%Z ≤ low (indexes1 r) ∧ low (indexes1 r) ≤ i ∧ i < j ∧ j ≤ high (indexes1 r) ∧ high (indexes1 r) ≤ Z.of_nat (length a) else ((match t with | Leaf _ => False | Node _ f f1 => f = r ∨ f1 = r end) ∧ is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) ∧ 0%Z ≤ low (indexes1 r) ∧ low (indexes1 r) ≤ m ∧ m < j ∧ j ≤ high (indexes1 r) ∧ high (indexes1 r) ≤ Z.of_nat (length a)) ∧ (match t with | Leaf _ => False | Node _ f f1 => f = l ∨ f1 = l end) ∧ is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) ∧ 0%Z ≤ low (indexes1 l) ∧ low (indexes1 l) ≤ i ∧ i < m ∧ m ≤ high (indexes1 l) ∧ high (indexes1 l) ≤ Z.of_nat (length a))) end) ∧ (∀(result : Z), (match t with | Leaf ind => result = isum ind | Node ind l r => (∃(o1 : bool), (if decide (i = low ind) then o1 = (if decide (j = high ind) then true else false) else o1 = false) ∧ (if decide (o1 = true) then result = isum ind else let m : Z := high (indexes1 l) in if decide (j ≤ m) then result = sum a i j else if decide (m ≤ i) then result = sum a i j else result = sum a i m + sum a m j)) end) -> result = sum a i j).
Admitted.
