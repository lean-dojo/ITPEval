(* Statement-only formalization of VERINA corpus artifact verina_basic_37,
   catalog title "findFirstOccurrence": an executable left-to-right search
   for the first occurrence of an integer in a nondecreasing integer array,
   returning its index or -1, together with the full correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted
  ZArith.

Import ListNotations.

Definition findFirstOccurrence_precond
    (arr : list Z) (_target : Z) : Prop :=
  StronglySorted Z.le arr.

Fixpoint findFirstOccurrence_loop
    (remaining : list Z) (target : Z) (i : nat) : Z :=
  match remaining with
  | [] => (-1)%Z
  | a :: rest =>
      if Z.eqb a target
      then Z.of_nat i
      else if Z.ltb target a
      then (-1)%Z
      else findFirstOccurrence_loop rest target (S i)
  end.

Definition findFirstOccurrence
    (arr : list Z)
    (target : Z)
    (_h_precond : findFirstOccurrence_precond arr target) : Z :=
  findFirstOccurrence_loop arr target 0%nat.

Definition findFirstOccurrence_postcond
    (arr : list Z)
    (target result : Z)
    (_h_precond : findFirstOccurrence_precond arr target) : Prop :=
  (result = (-1)%Z \/ (0 <= result)%Z) /\
  ((0 <= result)%Z ->
    (Z.to_nat result < length arr)%nat /\
    nth (Z.to_nat result) arr 0%Z = target /\
    forall i : nat,
      (i < Z.to_nat result)%nat ->
      nth i arr 0%Z <> target) /\
  (result = (-1)%Z ->
    forall i : nat,
      (i < length arr)%nat ->
      nth i arr 0%Z <> target).

Theorem findFirstOccurrence_spec_satisfied
    (arr : list Z)
    (target : Z)
    (h_precond : findFirstOccurrence_precond arr target) :
  findFirstOccurrence_postcond
    arr
    target
    (findFirstOccurrence arr target h_precond)
    h_precond.
Admitted.
