(* Statement-only formalization of VERINA corpus artifact verina_basic_51,
   catalog title "BinarySearch": executable lower-bound binary search for the
   insertion index of an integer in a nondecreasing integer array, together
   with its prefix/suffix ordering contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition BinarySearch_precond
    (a : list Z)
    (_key : Z) : Prop :=
  StronglySorted Z.le a.

Fixpoint binarySearchLoop_fuel
    (fuel : nat)
    (a : list Z)
    (key : Z)
    (lo hi : nat) : nat :=
  match fuel with
  | O => lo
  | S fuel' =>
      if Nat.ltb lo hi then
        let mid := Nat.div (Nat.add lo hi) 2%nat in
        if Z.ltb (nth mid a 0%Z) key
        then binarySearchLoop_fuel fuel' a key (S mid) hi
        else binarySearchLoop_fuel fuel' a key lo mid
      else
        lo
  end.

Definition binarySearchLoop
    (a : list Z)
    (key : Z)
    (lo hi : nat) : nat :=
  binarySearchLoop_fuel (S (Nat.sub hi lo)) a key lo hi.

Definition BinarySearch
    (a : list Z)
    (key : Z)
    (_h_precond : BinarySearch_precond a key) : nat :=
  binarySearchLoop a key 0%nat (length a).

Definition BinarySearch_postcond
    (a : list Z)
    (key : Z)
    (result : nat)
    (_h_precond : BinarySearch_precond a key) : Prop :=
  Nat.le result (length a) /\
  forallb (fun x => Z.ltb x key) (firstn result a) = true /\
  forallb (fun x => Z.leb key x) (skipn result a) = true.

Theorem BinarySearch_spec_satisfied
    (a : list Z)
    (key : Z)
    (h_precond : BinarySearch_precond a key) :
  BinarySearch_postcond
    a key (BinarySearch a key h_precond) h_precond.
Admitted.
