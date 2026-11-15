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
Require Import Why3.bintree.Tree.
Require Import Why3.bintree.Size.
Require Import Why3.bintree.Occ.
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
Definition le_root (e : elt) (t : tree elt) := match t with | Empty => True | Node _ x _ => le e x end.
Program Fixpoint heap (t : tree elt) : Prop :=
match t with | Empty => True | Node l x r => le_root x l ∧ heap l ∧ le_root x r ∧ heap r end.
Admit Obligations.
Axiom minimum : tree elt -> elt.
Axiom minimum_def : forall  (l : tree elt) (x : elt) (r : tree elt), minimum (Node l x r) = x.
Definition is_minimum (x : elt) (t : tree elt) := mem x t ∧ (∀(e : elt), mem e t -> le x e).
Axiom empty : tree elt.
Axiom empty'def : heap empty ∧ Size.size empty = 0%Z ∧ (∀(e : elt), ¬ mem e empty).
Theorem merge'vc (t1 : tree elt) (t2 : tree elt) (fact0 : heap t1) (fact1 : heap t2) : (match t2 with | Empty => (match t1 with | Empty => True | _ => True end) | Node x x1 x2 => (match t1 with | Empty => True | Node x3 x4 x5 => (if decide (le x4 x1) then (0%Z ≤ Size.size t1 + Size.size t2 ∧ Size.size x5 + Size.size t2 < Size.size t1 + Size.size t2) ∧ heap x5 ∧ heap t2 else (0%Z ≤ Size.size t1 + Size.size t2 ∧ Size.size x2 + Size.size t1 < Size.size t1 + Size.size t2) ∧ heap x2 ∧ heap t1) end) end) ∧ (∀(result : tree elt), (match t2 with | Empty => (match t1 with | Empty => result = t2 | _ => result = t1 end) | Node x x1 x2 => (match t1 with | Empty => result = t2 | Node x3 x4 x5 => (if decide (le x4 x1) then ∃(o1 : tree elt), (heap o1 ∧ (∀(e : elt), occ e o1 = occ e x5 + occ e t2) ∧ Size.size o1 = Size.size x5 + Size.size t2) ∧ result = Node o1 x4 x3 else ∃(o1 : tree elt), (heap o1 ∧ (∀(e : elt), occ e o1 = occ e x2 + occ e t1) ∧ Size.size o1 = Size.size x2 + Size.size t1) ∧ result = Node o1 x1 x) end) end) -> heap result ∧ (∀(e : elt), occ e result = occ e t1 + occ e t2) ∧ Size.size result = Size.size t1 + Size.size t2).
Admitted.
