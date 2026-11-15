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
Axiom elt : Type.
Axiom elt_inhabited : Inhabited elt.
Global Existing Instance elt_inhabited.
Axiom elt_countable : Countable elt.
Global Existing Instance elt_countable.
Axiom le : elt -> elt -> Prop.
Axiom Refl : forall  (x : elt), le x x.
Axiom Trans : forall  (x : elt) (y : elt) (z : elt) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom Total : forall  (x : elt) (y : elt), le x y ∨ le y x.
Inductive tree :=
  | tree'mk : elt -> list tree -> Z -> tree.
Axiom tree_inhabited : Inhabited tree.
Global Existing Instance tree_inhabited.
Axiom tree_countable : Countable tree.
Global Existing Instance tree_countable.
Definition elem (x : tree) := match x with |  tree'mk a _ _ => a end.
Definition children (x : tree) := match x with |  tree'mk _ a _ => a end.
Definition rank (x : tree) := match x with |  tree'mk _ _ a => a end.
Program Fixpoint size (l : list tree) : Z :=
match l with | [] => 0%Z | cons (tree'mk _ c _) r => 1%Z + size c + size r end.
Admit Obligations.
Program Fixpoint le_roots (e : elt) (l : list tree) : Prop :=
match l with | [] => True | cons t r => le e (elem t) ∧ le_roots e r end.
Admit Obligations.
Program Fixpoint heaps (l : list tree) : Prop :=
match l with | [] => True | cons (tree'mk e c _) r => le_roots e c ∧ heaps c ∧ heaps r end.
Admit Obligations.
Program Fixpoint occ (x : elt) (l : list tree) : Z :=
match l with | [] => 0%Z | cons (tree'mk y c _) r => (if decide (x = y) then 1%Z else 0%Z) + occ x c + occ x r end.
Admit Obligations.
Definition mem (x : elt) (l : list tree) := 0%Z < occ x l.
Program Fixpoint has_order (k : Z) (l : list tree) : Prop :=
match l with | [] => k = 0%Z | cons (tree'mk _ c k') r => k' = k - 1%Z ∧ has_order (k - 1%Z) c ∧ has_order (k - 1%Z) r end.
Admit Obligations.
Definition binomial_tree (t : tree) := rank t = Z.of_nat (length (children t)) ∧ has_order (rank t) (children t).
Axiom heap : Type.
Axiom heap_inhabited : Inhabited heap.
Global Existing Instance heap_inhabited.
Axiom heap_countable : Countable heap.
Global Existing Instance heap_countable.
Program Fixpoint inv (m : Z) (h : list tree) : Prop :=
match h with | [] => True | cons t r => (let k : Z := rank t in m ≤ k ∧ binomial_tree t ∧ inv (k + 1%Z) r) end.
Admit Obligations.
Definition link (t1 : tree) (t2 : tree) : tree := if decide (le (elem t1) (elem t2)) then tree'mk (elem t1) (cons t2 (children t1)) (rank t1 + 1%Z) else tree'mk (elem t2) (cons t1 (children t2)) (rank t2 + 1%Z).
Theorem extract_min_tree'vc (h : list tree) (k : Z) (fact0 : heaps h) (fact1 : inv k h) (fact2 : ¬ h = ([] : list tree)) : (match h with | [] => False | cons t [] => True | cons t tl => (match h with | [] => False | cons _ f => f = tl end) ∧ heaps tl ∧ inv (rank t + 1%Z) tl ∧ ¬ tl = ([] : list tree) end) ∧ (∀(t : tree) (h' : list tree), (match h with | [] => False | cons t1 [] => t = t1 ∧ h' = ([] : list tree) | cons t1 tl => (∃(t2 : tree) (h'1 : list tree), (heaps (cons t2 ([] : list tree)) ∧ heaps h'1 ∧ inv (rank t1 + 1%Z) h'1 ∧ le_roots (elem t2) tl ∧ binomial_tree t2 ∧ (∀(x : elt), occ x tl = occ x (cons t2 ([] : list tree)) + occ x h'1)) ∧ (if decide (le (elem t1) (elem t2)) then t = t1 ∧ h' = tl else t = t2 ∧ h' = cons t1 h'1)) end) -> heaps (cons t ([] : list tree)) ∧ heaps h' ∧ inv k h' ∧ le_roots (elem t) h ∧ binomial_tree t ∧ (∀(x : elt), occ x h = occ x (cons t ([] : list tree)) + occ x h')).
Admitted.
