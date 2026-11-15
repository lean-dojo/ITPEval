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
Require Import pairing_heap_vcg.pairing_heap.HeapType.
Require Import pairing_heap_vcg.pairing_heap.Size.
Require Import pairing_heap_vcg.pairing_heap.Occ.
Open Scope Z_scope.
Axiom le : elt -> elt -> Prop.
Axiom Refl : forall  (x : elt), le x x.
Axiom Trans : forall  (x : elt) (y : elt) (z : elt) (fact0 : le x y) (fact1 : le y z), le x z.
Axiom Total : forall  (x : elt) (y : elt), le x y ∨ le y x.
Definition le_tree (e : elt) (t : tree) := match t with | T x _ => le e x end.
Definition le_root (e : elt) (h : raw_heap) := match h with | E => True | H t => le_tree e t end.
Program Fixpoint le_roots (e : elt) (l : list tree) : Prop :=
match l with | [] => True | cons t r => le_tree e t ∧ le_roots e r end.
Admit Obligations.
Axiom heap : raw_heap -> Prop.
Axiom heap_tree : tree -> Prop.
Axiom heap_list : list tree -> Prop.
Axiom heap_def : forall (h : raw_heap), heap h = (match h with | E => True | H t => heap_tree t end).
Axiom heap_tree_def : forall (t : tree), heap_tree t = (match t with | T x l => le_roots x l ∧ heap_list l end).
Axiom heap_list_def : forall (l : list tree), heap_list l = (match l with | [] => True | cons t r => heap_tree t ∧ heap_list r end).
Axiom heap1 : Type.
Axiom heap1_inhabited : Inhabited heap1.
Global Existing Instance heap1_inhabited.
Axiom heap1_countable : Countable heap1.
Global Existing Instance heap1_countable.
Axiom h : heap1 -> raw_heap.
Axiom heap'invariant : forall  (self : heap1), heap (h self).
Definition heap'eq (a : heap1) (b : heap1) := h a = h b.
Axiom heap'inj : forall  (a : heap1) (b : heap1) (fact0 : heap'eq a b), a = b.
Definition size (hh : heap1) : Z := size_heap (h hh).
Definition occ (e : elt) (hh : heap1) : Z := occ_heap e (h hh).
Definition is_minimum_tree (x : elt) (t : tree) := mem_tree x t ∧ (∀(e : elt), mem_tree e t -> le x e).
Definition is_minimum (x : elt) (h1 : raw_heap) := mem x h1 ∧ (∀(e : elt), mem e h1 -> le x e).
Axiom minimum_tree : tree -> elt.
Axiom minimum_tree_def : forall  (x : elt) (l : list tree), minimum_tree (T x l) = x.
Axiom minimum : raw_heap -> elt.
Axiom minimum_def : forall  (t : tree), minimum (H t) = minimum_tree t.
Definition minimum_heap (hh : heap1) : elt := minimum (h hh).
Axiom empty : heap1.
Axiom empty'def : size_heap (h empty) = 0%Z ∧ (∀(e : elt), ¬ mem e (h empty)).
Theorem delete_min'vc (hh : heap1) (fact0 : 0%Z < size_heap (h hh)) : let o1 : raw_heap := h hh in (match o1 with | E => False | H (T _ l) => heap_list l end) ∧ (∀(result : heap1), (match o1 with | E => False | H (T _ l) => size_heap (h result) = size_list l ∧ (∀(x : elt), occ_heap x (h result) = occ_list x l) end) -> occ_heap (minimum (h hh)) (h result) = occ_heap (minimum (h hh)) (h hh) - 1%Z ∧ (∀(y : elt), ¬ y = minimum (h hh) -> occ_heap y (h result) = occ_heap y (h hh)) ∧ size_heap (h result) = size_heap (h hh) - 1%Z).
Admitted.
