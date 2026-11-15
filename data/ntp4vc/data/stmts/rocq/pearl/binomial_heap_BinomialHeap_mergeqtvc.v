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
Axiom size : list tree -> Z.
Axiom size_def : forall (l : list tree), size l = (match l with | [] => 0%Z | cons (tree'mk _ c _) r => 1%Z + size c + size r end).
Axiom le_roots : elt -> list tree -> Prop.
Axiom le_roots_def : forall (e : elt) (l : list tree), le_roots e l = (match l with | [] => True | cons t r => le e (elem t) ∧ le_roots e r end).
Axiom heaps : list tree -> Prop.
Axiom heaps_def : forall (l : list tree), heaps l = (match l with | [] => True | cons (tree'mk e c _) r => le_roots e c ∧ heaps c ∧ heaps r end).
Axiom occ : elt -> list tree -> Z.
Axiom occ_def : forall (x : elt) (l : list tree), occ x l = (match l with | [] => 0%Z | cons (tree'mk y c _) r => (if decide (x = y) then 1%Z else 0%Z) + occ x c + occ x r end).
Definition mem (x : elt) (l : list tree) := 0%Z < occ x l.
Axiom has_order : Z -> list tree -> Prop.
Axiom has_order_def : forall (k : Z) (l : list tree), has_order k l = (match l with | [] => k = 0%Z | cons (tree'mk _ c k') r => k' = k - 1%Z ∧ has_order (k - 1%Z) c ∧ has_order (k - 1%Z) r end).
Definition binomial_tree (t : tree) := rank t = Z.of_nat (length (children t)) ∧ has_order (rank t) (children t).
Axiom heap : Type.
Axiom heap_inhabited : Inhabited heap.
Global Existing Instance heap_inhabited.
Axiom heap_countable : Countable heap.
Global Existing Instance heap_countable.
Axiom inv : Z -> list tree -> Prop.
Axiom inv_def : forall (m : Z) (h : list tree), inv m h = (match h with | [] => True | cons t r => (let k : Z := rank t in m ≤ k ∧ binomial_tree t ∧ inv (k + 1%Z) r) end).
Definition link (t1 : tree) (t2 : tree) : tree := if decide (le (elem t1) (elem t2)) then tree'mk (elem t1) (cons t2 (children t1)) (rank t1 + 1%Z) else tree'mk (elem t2) (cons t1 (children t2)) (rank t2 + 1%Z).
Theorem merge'vc (h1 : list tree) (k : Z) (h2 : list tree) (fact0 : heaps h1) (fact1 : inv k h1) (fact2 : heaps h2) (fact3 : inv k h2) : (match h2 with | [] => (match h1 with | [] => True | _ => True end) | cons x x1 => (match h1 with | [] => True | cons x2 x3 => (if decide (rank x2 < rank x) then let o1 : Z := rank x2 + 1%Z in (match h1 with | [] => False | cons _ f => f = x3 end) ∧ heaps x3 ∧ inv o1 x3 ∧ heaps h2 ∧ inv o1 h2 else if decide (rank x < rank x2) then let o1 : Z := rank x + 1%Z in (match h2 with | [] => False | cons _ f => f = x1 end) ∧ heaps h1 ∧ inv o1 h1 ∧ heaps x1 ∧ inv o1 x1 else let o1 : Z := rank x2 + 1%Z in (((match h1 with | [] => False | cons _ f => f = x3 end) ∨ h1 = x3 ∧ (match h2 with | [] => False | cons _ f => f = x1 end)) ∧ heaps x3 ∧ inv o1 x3 ∧ heaps x1 ∧ inv o1 x1) ∧ (∀(o2 : list tree), heaps o2 ∧ inv o1 o2 ∧ (∀(x4 : elt), occ x4 o2 = occ x4 x3 + occ x4 x1) -> (let o3 : tree := link x2 x in heaps (cons o3 ([] : list tree)) ∧ binomial_tree o3 ∧ heaps o2 ∧ inv (rank o3) o2))) end) end) ∧ (∀(result : list tree), (match h2 with | [] => (match h1 with | [] => result = h2 | _ => result = h1 end) | cons x x1 => (match h1 with | [] => result = h2 | cons x2 x3 => (if decide (rank x2 < rank x) then ∃(o1 : list tree), (heaps o1 ∧ inv (rank x2 + 1%Z) o1 ∧ (∀(x4 : elt), occ x4 o1 = occ x4 x3 + occ x4 h2)) ∧ result = cons x2 o1 else if decide (rank x < rank x2) then ∃(o1 : list tree), (heaps o1 ∧ inv (rank x + 1%Z) o1 ∧ (∀(x4 : elt), occ x4 o1 = occ x4 h1 + occ x4 x1)) ∧ result = cons x o1 else ∃(o1 : list tree), (heaps o1 ∧ inv (rank x2 + 1%Z) o1 ∧ (∀(x4 : elt), occ x4 o1 = occ x4 x3 + occ x4 x1)) ∧ (let o2 : tree := link x2 x in heaps result ∧ inv (rank o2) result ∧ (∀(x4 : elt), occ x4 result = occ x4 (cons o2 ([] : list tree)) + occ x4 o1))) end) end) -> heaps result ∧ inv k result ∧ (∀(x : elt), occ x result = occ x h1 + occ x h2)).
Admitted.
