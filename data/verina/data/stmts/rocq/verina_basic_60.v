(* Statement-only formalization of VERINA corpus artifact verina_basic_60,
   catalog title "FindEvenNumbers": an executable left-to-right scan that
   extracts exactly the even integers from an arbitrary integer array while
   preserving their order, together with its correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition isEven (n : Z) : bool :=
  Z.eqb (Z.modulo n 2%Z) 0%Z.

Definition FindEvenNumbers_precond (_arr : list Z) : Prop :=
  True.

Fixpoint FindEvenNumbers_loop
    (remaining acc : list Z) : list Z :=
  match remaining with
  | [] => acc
  | x :: xs =>
      FindEvenNumbers_loop
        xs
        (if isEven x then acc ++ [x] else acc)
  end.

Definition FindEvenNumbers
    (arr : list Z)
    (_h_precond : FindEvenNumbers_precond arr) : list Z :=
  FindEvenNumbers_loop arr [].

Inductive list_sublist {A : Type} : list A -> list A -> Prop :=
| list_sublist_nil :
    list_sublist [] []
| list_sublist_cons :
    forall (x : A) (xs ys : list A),
      list_sublist xs ys ->
      list_sublist (x :: xs) (x :: ys)
| list_sublist_skip :
    forall (x : A) (xs ys : list A),
      list_sublist xs ys ->
      list_sublist xs (x :: ys).

Fixpoint countP {A : Type}
    (p : A -> bool)
    (xs : list A) : nat :=
  match xs with
  | [] => 0%nat
  | x :: rest =>
      if p x then S (countP p rest) else countP p rest
  end.

Definition FindEvenNumbers_postcond
    (arr result : list Z)
    (_h_precond : FindEvenNumbers_precond arr) : Prop :=
  forallb isEven result = true /\
  list_sublist result arr /\
  length result = countP isEven arr.

Theorem FindEvenNumbers_spec_satisfied
    (arr : list Z)
    (h_precond : FindEvenNumbers_precond arr) :
  FindEvenNumbers_postcond
    arr (FindEvenNumbers arr h_precond) h_precond.
Admitted.
