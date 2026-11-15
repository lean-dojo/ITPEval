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
Open Scope Z_scope.
Inductive tree :=
  | Empty : tree
  | Node : tree -> Z -> tree -> tree.
Axiom tree_inhabited : Inhabited tree.
Global Existing Instance tree_inhabited.
Axiom tree_countable : Countable tree.
Global Existing Instance tree_countable.
Program Fixpoint size (t : tree) : Z :=
match t with | Empty => 0%Z | Node l _ r => 1%Z + size l + size r end.
Admit Obligations.
Program Fixpoint mem (x : Z) (t : tree) : Prop :=
match t with | Empty => False | Node l v r => mem x l ∨ x = v ∨ mem x r end.
Admit Obligations.
Theorem maximum'vc (t : tree) (fact0 : ¬ t = (Empty : tree)) : (match t with | Empty => False | Node Empty v Empty => True | Node Empty v s => (0%Z ≤ size t ∧ size s < size t) ∧ ¬ s = (Empty : tree) | Node s v Empty => (0%Z ≤ size t ∧ size s < size t) ∧ ¬ s = (Empty : tree) | Node l v r => ((0%Z ≤ size t ∧ size r < size t) ∧ ¬ r = (Empty : tree)) ∧ (∀(o1 : Z), mem o1 r ∧ (∀(x : Z), mem x r -> x ≤ o1) -> (0%Z ≤ size t ∧ size l < size t) ∧ ¬ l = (Empty : tree)) end) ∧ (∀(result : Z), (match t with | Empty => False | Node Empty v Empty => result = v | Node Empty v s => (∃(o1 : Z), (mem o1 s ∧ (∀(x : Z), mem x s -> x ≤ o1)) ∧ result = Z.max o1 v) | Node s v Empty => (∃(o1 : Z), (mem o1 s ∧ (∀(x : Z), mem x s -> x ≤ o1)) ∧ result = Z.max o1 v) | Node l v r => (∃(o1 : Z), (mem o1 r ∧ (∀(x : Z), mem x r -> x ≤ o1)) ∧ (∃(o2 : Z), (mem o2 l ∧ (∀(x : Z), mem x l -> x ≤ o2)) ∧ result = Z.max o2 (Z.max v o1))) end) -> mem result t ∧ (∀(x : Z), mem x t -> x ≤ result)).
Admitted.
