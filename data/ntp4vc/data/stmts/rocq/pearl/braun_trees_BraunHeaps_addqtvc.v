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
Program Fixpoint inv (t : tree elt) : Prop :=
match t with | Empty => True | Node l _ r => (Size.size l = Size.size r ∨ Size.size l = Size.size r + 1%Z) ∧ inv l ∧ inv r end.
Admit Obligations.
Axiom empty : tree elt.
Axiom empty'def : heap empty ∧ inv empty ∧ Size.size empty = 0%Z ∧ (∀(e : elt), ¬ mem e empty).
Theorem add'vc (t : tree elt) (x : elt) (fact0 : heap t) (fact1 : inv t) : (match t with | Empty => True | Node l y r => (match t with | Empty => False | Node f _ f1 => f = r ∨ f1 = r end) ∧ heap r ∧ inv r end) ∧ (∀(result : tree elt), (match t with | Empty => result = Node (Empty : tree elt) x (Empty : tree elt) | Node l y r => (if decide (le x y) then ∃(o1 : tree elt), (heap o1 ∧ inv o1 ∧ occ y o1 = occ y r + 1%Z ∧ (∀(e : elt), ¬ e = y -> occ e o1 = occ e r) ∧ Size.size o1 = Size.size r + 1%Z) ∧ result = Node o1 x l else ∃(o1 : tree elt), (heap o1 ∧ inv o1 ∧ occ x o1 = occ x r + 1%Z ∧ (∀(e : elt), ¬ e = x -> occ e o1 = occ e r) ∧ Size.size o1 = Size.size r + 1%Z) ∧ result = Node o1 y l) end) -> heap result ∧ inv result ∧ occ x result = occ x t + 1%Z ∧ (∀(e : elt), ¬ e = x -> occ e result = occ e t) ∧ Size.size result = Size.size t + 1%Z).
Admitted.
