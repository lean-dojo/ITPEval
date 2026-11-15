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
Program Fixpoint depth (t : tree) : Z :=
match t with | Leaf _ => 1%Z | Node _ l r => 1%Z + Z.max (depth l) (depth r) end.
Admit Obligations.
Theorem query_aux_complexity'vc (t : tree) (a : list Z) (i : Z) (j : Z) (c : Z) (fact0 : is_tree_for t a (low (indexes1 t)) (high (indexes1 t))) (fact1 : 0%Z ≤ low (indexes1 t)) (fact2 : low (indexes1 t) ≤ i) (fact3 : i < j) (fact4 : j ≤ high (indexes1 t)) (fact5 : high (indexes1 t) ≤ Z.of_nat (length a)) : match t with | Leaf ind => c + 1%Z - c ≤ (if decide (i = low (indexes1 t) ∧ j = high (indexes1 t)) then 1%Z else if decide (i = low (indexes1 t) ∨ j = high (indexes1 t)) then 2%Z * depth t else 4%Z * depth t) ∧ isum ind = sum a i j | Node ind l r => (∀(o1 : bool), (if decide (i = low ind) then o1 = (if decide (j = high ind) then true else false) else o1 = false) -> (if decide (o1 = true) then c + 1%Z - c ≤ (if decide (i = low (indexes1 t) ∧ j = high (indexes1 t)) then 1%Z else if decide (i = low (indexes1 t) ∨ j = high (indexes1 t)) then 2%Z * depth t else 4%Z * depth t) ∧ isum ind = sum a i j else let m : Z := high (indexes1 l) in if decide (j ≤ m) then ((match t with | Leaf _ => False | Node _ f f1 => f = l ∨ f1 = l end) ∧ is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) ∧ 0%Z ≤ low (indexes1 l) ∧ low (indexes1 l) ≤ i ∧ i < j ∧ j ≤ high (indexes1 l) ∧ high (indexes1 l) ≤ Z.of_nat (length a)) ∧ (∀(c1 : Z), c1 - (c + 1%Z) ≤ (if decide (i = low (indexes1 l) ∧ j = high (indexes1 l)) then 1%Z else if decide (i = low (indexes1 l) ∨ j = high (indexes1 l)) then 2%Z * depth l else 4%Z * depth l) -> c1 - c ≤ (if decide (i = low (indexes1 t) ∧ j = high (indexes1 t)) then 1%Z else if decide (i = low (indexes1 t) ∨ j = high (indexes1 t)) then 2%Z * depth t else 4%Z * depth t)) else if decide (m ≤ i) then ((match t with | Leaf _ => False | Node _ f f1 => f = r ∨ f1 = r end) ∧ is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) ∧ 0%Z ≤ low (indexes1 r) ∧ low (indexes1 r) ≤ i ∧ i < j ∧ j ≤ high (indexes1 r) ∧ high (indexes1 r) ≤ Z.of_nat (length a)) ∧ (∀(c1 : Z), c1 - (c + 1%Z) ≤ (if decide (i = low (indexes1 r) ∧ j = high (indexes1 r)) then 1%Z else if decide (i = low (indexes1 r) ∨ j = high (indexes1 r)) then 2%Z * depth r else 4%Z * depth r) -> c1 - c ≤ (if decide (i = low (indexes1 t) ∧ j = high (indexes1 t)) then 1%Z else if decide (i = low (indexes1 t) ∨ j = high (indexes1 t)) then 2%Z * depth t else 4%Z * depth t)) else ((match t with | Leaf _ => False | Node _ f f1 => f = r ∨ f1 = r end) ∧ is_tree_for r a (low (indexes1 r)) (high (indexes1 r)) ∧ 0%Z ≤ low (indexes1 r) ∧ low (indexes1 r) ≤ m ∧ m < j ∧ j ≤ high (indexes1 r) ∧ high (indexes1 r) ≤ Z.of_nat (length a)) ∧ (∀(c1 : Z), c1 - (c + 1%Z) ≤ (if decide (m = low (indexes1 r) ∧ j = high (indexes1 r)) then 1%Z else if decide (m = low (indexes1 r) ∨ j = high (indexes1 r)) then 2%Z * depth r else 4%Z * depth r) -> ((match t with | Leaf _ => False | Node _ f f1 => f = l ∨ f1 = l end) ∧ is_tree_for l a (low (indexes1 l)) (high (indexes1 l)) ∧ 0%Z ≤ low (indexes1 l) ∧ low (indexes1 l) ≤ i ∧ i < m ∧ m ≤ high (indexes1 l) ∧ high (indexes1 l) ≤ Z.of_nat (length a)) ∧ (∀(c2 : Z), c2 - c1 ≤ (if decide (i = low (indexes1 l) ∧ m = high (indexes1 l)) then 1%Z else if decide (i = low (indexes1 l) ∨ m = high (indexes1 l)) then 2%Z * depth l else 4%Z * depth l) -> c2 - c ≤ (if decide (i = low (indexes1 t) ∧ j = high (indexes1 t)) then 1%Z else if decide (i = low (indexes1 t) ∨ j = high (indexes1 t)) then 2%Z * depth t else 4%Z * depth t) ∧ sum a i m + sum a m j = sum a i j)))) end.
Admitted.
