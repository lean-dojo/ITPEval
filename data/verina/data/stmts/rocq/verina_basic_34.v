(* Statement-only formalization of VERINA corpus artifact verina_basic_34,
   catalog title "findEvenNumbers": an executable stable filter that extracts
   the even integers from an integer array, together with its trivial
   precondition, multiplicity and order postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition isEven (n : Z) : bool :=
  Z.eqb (Z.modulo n 2%Z) 0%Z.

Definition findEvenNumbers_precond (_arr : list Z) : Prop :=
  True.

Definition findEvenNumbers_step
    (acc : list Z)
    (x : Z) : list Z :=
  if isEven x then acc ++ [x] else acc.

Definition findEvenNumbers
    (arr : list Z)
    (_h_precond : findEvenNumbers_precond arr) : list Z :=
  fold_left findEvenNumbers_step arr [].

Fixpoint findEvenNumbers_idxOf
    (x : Z)
    (xs : list Z) : nat :=
  match xs with
  | [] => 0%nat
  | y :: ys =>
      if Z.eqb x y
      then 0%nat
      else S (findEvenNumbers_idxOf x ys)
  end.

Definition findEvenNumbers_postcond
    (arr result : list Z)
    (_h_precond : findEvenNumbers_precond arr) : Prop :=
  Forall
    (fun x =>
      isEven x = true /\
      In x arr /\
      count_occ Z.eq_dec result x = count_occ Z.eq_dec arr x)
    result /\
  Forall
    (fun x =>
      isEven x = true ->
      In x result)
    arr /\
  Forall
    (fun x =>
      Forall
        (fun y =>
          isEven x = true ->
          isEven y = true ->
          (findEvenNumbers_idxOf x arr <=
           findEvenNumbers_idxOf y arr)%nat ->
          (findEvenNumbers_idxOf x result <=
           findEvenNumbers_idxOf y result)%nat)
        arr)
    arr.

Theorem findEvenNumbers_spec_satisfied
    (arr : list Z)
    (h_precond : findEvenNumbers_precond arr) :
  findEvenNumbers_postcond
    arr (findEvenNumbers arr h_precond) h_precond.
Admitted.
