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
Theorem tree_of_array'vc (i : Z) (j : Z) (a : list Z) (fact0 : 0%Z ≤ i) (fact1 : i < j) (fact2 : j ≤ Z.of_nat (length a)) : let o1 : Z := i + 1%Z in (if decide (o1 = j) then 0%Z ≤ i ∧ i < Z.of_nat (length a) else ¬ 2%Z = 0%Z ∧ (let m : Z := Z.rem (i + j) 2%Z in ((0%Z ≤ j - i ∧ m - i < j - i) ∧ 0%Z ≤ i ∧ i < m ∧ m ≤ Z.of_nat (length a)) ∧ (∀(l : tree), is_tree_for l a i m -> (0%Z ≤ j - i ∧ j - m < j - i) ∧ 0%Z ≤ m ∧ m < j ∧ j ≤ Z.of_nat (length a)))) ∧ (∀(result : tree), (if decide (o1 = j) then result = Leaf (indexes'mk i j (nth (Z.to_nat i) a inhabitant)) else let m : Z := Z.rem (i + j) 2%Z in ∃(l : tree), is_tree_for l a i m ∧ (∃(r : tree), is_tree_for r a m j ∧ result = Node (indexes'mk i j (isum (indexes1 l) + isum (indexes1 r))) l r)) -> is_tree_for result a i j).
Admitted.
