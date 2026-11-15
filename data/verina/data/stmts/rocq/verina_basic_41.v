(* Statement-only formalization of VERINA corpus artifact verina_basic_41,
   catalog title "hasOnlyOneDistinctElement": an executable Boolean scan of a
   nonempty integer array that tests whether every element equals its first,
   together with its pairwise-equality and differing-element correctness
   contract and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition hasOnlyOneDistinctElement_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Fixpoint hasOnlyOneDistinctElement_loop
    (first : Z) (remaining : list Z) : bool :=
  match remaining with
  | [] => true
  | x :: xs =>
      if Z.eqb x first
      then hasOnlyOneDistinctElement_loop first xs
      else false
  end.

Definition hasOnlyOneDistinctElement
    (a : list Z)
    (_h_precond : hasOnlyOneDistinctElement_precond a) : bool :=
  match a with
  | [] => true
  | first :: rest => hasOnlyOneDistinctElement_loop first rest
  end.

Fixpoint hasOnlyOneDistinctElement_pairwise_eq
    (values : list Z) : Prop :=
  match values with
  | [] => True
  | first :: rest =>
      Forall (fun x => first = x) rest /\
      hasOnlyOneDistinctElement_pairwise_eq rest
  end.

Definition hasOnlyOneDistinctElement_any_difference
    (values : list Z) : bool :=
  existsb
    (fun x => negb (Z.eqb x (nth 0 values 0%Z)))
    values.

Definition hasOnlyOneDistinctElement_postcond
    (a : list Z)
    (result : bool)
    (_h_precond : hasOnlyOneDistinctElement_precond a) : Prop :=
  (Is_true result ->
    hasOnlyOneDistinctElement_pairwise_eq a) /\
  (~ Is_true result ->
    Is_true (hasOnlyOneDistinctElement_any_difference a)).

Theorem hasOnlyOneDistinctElement_spec_satisfied
    (a : list Z)
    (h_precond : hasOnlyOneDistinctElement_precond a) :
  hasOnlyOneDistinctElement_postcond
    a
    (hasOnlyOneDistinctElement a h_precond)
    h_precond.
Admitted.
