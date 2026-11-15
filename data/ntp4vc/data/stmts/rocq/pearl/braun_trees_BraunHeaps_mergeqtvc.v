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
Theorem merge'vc (l : tree elt) (r : tree elt) (fact0 : heap l) (fact1 : heap r) (fact2 : inv l) (fact3 : inv r) (fact4 : Size.size r ≤ Size.size l) (fact5 : Size.size l ≤ Size.size r + 1%Z) : (match r with | Empty => (match l with | Empty => True | _ => True end) | Node x x1 x2 => (match l with | Node x3 x4 x5 => (if decide (le x4 x1) then (0%Z ≤ Size.size l + Size.size r ∧ Size.size x3 + Size.size x5 < Size.size l + Size.size r) ∧ (heap x3 ∧ heap x5) ∧ (inv x3 ∧ inv x5) ∧ Size.size x5 ≤ Size.size x3 ∧ Size.size x3 ≤ Size.size x5 + 1%Z else (heap l ∧ inv l ∧ 0%Z < Size.size l) ∧ (∀(x6 : elt) (l1 : tree elt), heap l1 ∧ inv l1 ∧ Size.size l1 = Size.size l - 1%Z ∧ occ x6 l1 = occ x6 l - 1%Z ∧ (∀(x7 : elt), ¬ x7 = x6 -> occ x7 l1 = occ x7 l) -> heap r ∧ inv r ∧ 0%Z < Size.size r)) | Empty => False end) end) ∧ (∀(result : tree elt), (match r with | Empty => (match l with | Empty => result = l | _ => result = l end) | Node x x1 x2 => (match l with | Node x3 x4 x5 => (if decide (le x4 x1) then ∃(o1 : tree elt), (heap o1 ∧ inv o1 ∧ (∀(e : elt), occ e o1 = occ e x3 + occ e x5) ∧ Size.size o1 = Size.size x3 + Size.size x5) ∧ result = Node r x4 o1 else ∃(e : elt) (t' : tree elt), (heap t' ∧ inv t' ∧ Size.size t' = Size.size l - 1%Z ∧ occ e t' = occ e l - 1%Z ∧ (∀(x6 : elt), ¬ x6 = e -> occ x6 t' = occ x6 l)) ∧ (∃(o1 : tree elt), (heap o1 ∧ inv o1 ∧ (if decide (e = minimum r) then occ e o1 = occ e r else occ e o1 = occ e r + 1%Z ∧ occ (minimum r) o1 = occ (minimum r) r - 1%Z) ∧ (∀(e1 : elt), ¬ e1 = e -> ¬ e1 = minimum r -> occ e1 o1 = occ e1 r) ∧ Size.size o1 = Size.size r) ∧ result = Node o1 x1 t')) | Empty => False end) end) -> heap result ∧ inv result ∧ (∀(e : elt), occ e result = occ e l + occ e r) ∧ Size.size result = Size.size l + Size.size r).
Admitted.
