(*
MIT License

Copyright (c) 2017 Jean-Marie Madiot, INRIA

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)

Require Import Lists.List.
Require Import ZArith.
Require Import Setoid.
Require Import Coq.Classes.Morphisms.
Require Import Lia.

Open Scope Z_scope.
Import ListNotations.

(**

 Short proof of the inclusion-exclusion principle, which gives the
 cardinality of a finite union of finite sets as an alternating sum of
 cardinalities of the intersections of those sets.

 We choose a formalization of finite sets particularly well suited for
 our purposes: [X] is the universe, or support, of the base sets. We
 suppose the union is finite, and hence we assume a list [enum_X] to
 enumerate all the elements that are in all the considered sets.  In
 fact, we only use [enum_X] to define a constructive [cardinal]
 function, so if enum_X happens to enumerate some elements several
 times, the theorem still holds, which means that it also works if the
 cardinality is "weighted".
 
 Finally, the finiteness of the set of sets is enforced by using a
 list of sets, in which we do not require each set to be unique, so
 the inclusion-exclusion principle also works for a multiset of sets.

*)

Section InclusionExclusion.

Variable X : Set.
Variable enum_X : list X.

Definition set := X -> bool.

Definition cardinal (A : set) := Z.of_nat (length (filter A enum_X)).

Definition empty_set : set := fun _ => false.

Definition binary_union (A B : set) x := orb (A x) (B x).

Definition binary_intersection (A B : set) x := andb (A x) (B x).

Infix " ∪ " := binary_union (at level 50).

Infix " ∩ " := binary_intersection (at level 50).

Notation " # " := cardinal.

Lemma cardinal_union_lemma A B : # (A ∪ B) = # A + # B - # (A ∩ B).
Proof.
Admitted.

Definition list_union (A : list set) :=
  fold_right binary_union empty_set A.

Definition fold1 {A} (f : A -> A -> A) (l : list A) (default : A) :=
  match l with
  | nil => default
  | x :: xs => fold_right f x xs
  end.

Definition list_intersection (A : list set) :=
  fold1 binary_intersection A empty_set.

Definition set_eq (A B : set) := forall x, A x = B x.
Infix " == " := set_eq (at level 90).

Lemma set_eq_refl : Reflexive set_eq.
Proof.
Admitted.

Lemma set_eq_sym : Symmetric set_eq.
Proof.
Admitted.

Lemma set_eq_trans : Transitive set_eq.
Proof.
Admitted.

Add Parametric Relation : set set_eq
    reflexivity proved by set_eq_refl
    symmetry proved by set_eq_sym
    transitivity proved by set_eq_trans
      as Set_eq.

Instance union_morphism :
  Proper (set_eq ==> set_eq ==> set_eq) binary_union | 10.
Proof.
Admitted.

Instance intersection_morphism :
  Proper (set_eq ==> set_eq ==> set_eq) binary_intersection | 10.
Proof.
Admitted.

Instance cardinal_morphism :
  Proper (set_eq ==> @eq Z) cardinal | 10.
Proof.
Admitted.

Lemma cardinal_set_eq (A B : set) : A == B -> # A = # B.
Proof.
Admitted.

Ltac iftac :=
  let x := fresh "x" in
  intro x; compute;
  repeat
    match goal with
      |- context [ if ?b x then _ else _] => destruct b
    end; try reflexivity.

Ltac Rewrite H :=
  let E := fresh "E" in
  assert (E : H) by iftac; rewrite E; clear E.

Lemma cardinal_ternary_union A B C :
  # (A ∪ B ∪ C) = # A + # B + # C - # (A ∩ B) - #(B ∩ C) - # (C ∩ A) + #(A ∩ B ∩ C).
Proof.
Admitted.

Fixpoint sublists {A} (xs : list A) : list (list A) :=
  match xs with
  | nil => [[]]
  | x :: xs =>
    let xss := sublists xs in
    xss ++ (map (fun l => x :: l)) xss
  end.

Definition nonempty {A} (xs : list A) :=
  match xs with
    [] => false
  | _ :: _ => true
  end.

Fixpoint sum l :=
  match l with
  | nil => 0
  | x :: l => x + sum l
  end.

Fixpoint alternating_sign n :=
  match n with
  | O => 1
  | S n => - alternating_sign n
  end.

Lemma cardinal_empty : cardinal empty_set = 0.
Proof.
Admitted.

Lemma sum_app l1 l2 : sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
Admitted.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
Admitted.

Lemma filter_map_always {A B} f (g : A -> B) l :
  (forall x, f (g x) = true) ->
  filter f (map g l) = map g l.
Proof.
Admitted.

Lemma sublists_proper {A} (l : list A) :
  sublists l = [] :: filter nonempty (sublists l).
Proof.
Admitted.

Lemma sublists_map {A B} (f : A -> B) l :
  sublists (map f l) = map (map f) (sublists l).
Proof.
Admitted.

Theorem inclusion_exclusion (l : list set) :
  cardinal (list_union l) =
  sum
    (map (fun l' => cardinal (list_intersection l') *
                 alternating_sign (1 + length l'))
         (filter nonempty (sublists l))).
Proof.
Admitted.

End InclusionExclusion.

Arguments list_union [X].
Arguments list_intersection [X].
Arguments cardinal [X] [enum_X].
