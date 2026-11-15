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
Theorem replace_min'vc (t : tree elt) (x : elt) (fact0 : heap t) (fact1 : inv t) (fact2 : 0%Z < Size.size t) : (match t with | Node l _ r => (∀(o1 : bool), (if decide (le_root x l) then o1 = (if decide (le_root x r) then true else false) else o1 = false) -> ¬ o1 = true -> (heap l ∧ 0%Z < Size.size l) ∧ (if decide (le_root (minimum l) r) then (match t with | Empty => False | Node f _ f1 => f = l ∨ f1 = l end) ∧ heap l ∧ inv l ∧ 0%Z < Size.size l else ((match t with | Empty => False | Node f _ f1 => f = r ∨ f1 = r end) ∧ heap r ∧ inv r ∧ 0%Z < Size.size r) ∧ (∀(o2 : tree elt), heap o2 ∧ inv o2 ∧ (if decide (x = minimum r) then occ x o2 = occ x r else occ x o2 = occ x r + 1%Z ∧ occ (minimum r) o2 = occ (minimum r) r - 1%Z) ∧ (∀(e : elt), ¬ e = x -> ¬ e = minimum r -> occ e o2 = occ e r) ∧ Size.size o2 = Size.size r -> heap r ∧ 0%Z < Size.size r))) | Empty => False end) ∧ (∀(result : tree elt), (match t with | Node l _ r => (∃(o1 : bool), (if decide (le_root x l) then o1 = (if decide (le_root x r) then true else false) else o1 = false) ∧ (if decide (o1 = true) then result = Node l x r else let lx : elt := minimum l in if decide (le_root lx r) then ∃(o2 : tree elt), (heap o2 ∧ inv o2 ∧ (if decide (x = minimum l) then occ x o2 = occ x l else occ x o2 = occ x l + 1%Z ∧ occ (minimum l) o2 = occ (minimum l) l - 1%Z) ∧ (∀(e : elt), ¬ e = x -> ¬ e = minimum l -> occ e o2 = occ e l) ∧ Size.size o2 = Size.size l) ∧ result = Node o2 lx r else ∃(o2 : tree elt), (heap o2 ∧ inv o2 ∧ (if decide (x = minimum r) then occ x o2 = occ x r else occ x o2 = occ x r + 1%Z ∧ occ (minimum r) o2 = occ (minimum r) r - 1%Z) ∧ (∀(e : elt), ¬ e = x -> ¬ e = minimum r -> occ e o2 = occ e r) ∧ Size.size o2 = Size.size r) ∧ result = Node l (minimum r) o2)) | Empty => False end) -> heap result ∧ inv result ∧ (if decide (x = minimum t) then occ x result = occ x t else occ x result = occ x t + 1%Z ∧ occ (minimum t) result = occ (minimum t) t - 1%Z) ∧ (∀(e : elt), ¬ e = x -> ¬ e = minimum t -> occ e result = occ e t) ∧ Size.size result = Size.size t).
Admitted.
