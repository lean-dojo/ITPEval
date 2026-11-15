(* Statement-only formalization of VERINA corpus artifact verina_basic_20,
   catalog title "uniqueProduct": an executable left-to-right scan of an
   integer array that multiplies each distinct value exactly once, together
   with its trivial precondition, duplicate-erasure product postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition uniqueProduct_precond (_arr : list Z) : Prop :=
  True.

Fixpoint uniqueProduct_loop
    (remaining seen : list Z)
    (product : Z) : Z :=
  match remaining with
  | [] => product
  | x :: xs =>
      if existsb (fun y => Z.eqb y x) seen
      then uniqueProduct_loop xs seen product
      else uniqueProduct_loop xs (x :: seen) (product * x)
  end.

Definition uniqueProduct
    (arr : list Z)
    (_h_precond : uniqueProduct_precond arr) : Z :=
  uniqueProduct_loop arr [] 1%Z.

Fixpoint uniqueProduct_eraseDups_aux
    (seen remaining : list Z) : list Z :=
  match remaining with
  | [] => []
  | x :: xs =>
      if existsb (fun y => Z.eqb y x) seen
      then uniqueProduct_eraseDups_aux seen xs
      else x :: uniqueProduct_eraseDups_aux (x :: seen) xs
  end.

Definition uniqueProduct_eraseDups
    (arr : list Z) : list Z :=
  uniqueProduct_eraseDups_aux [] arr.

Definition uniqueProduct_list_product
    (xs : list Z) : Z :=
  fold_left Z.mul xs 1%Z.

Definition uniqueProduct_postcond
    (arr : list Z)
    (result : Z)
    (_h_precond : uniqueProduct_precond arr) : Prop :=
  result - uniqueProduct_list_product (uniqueProduct_eraseDups arr) = 0%Z /\
  uniqueProduct_list_product (uniqueProduct_eraseDups arr) - result = 0%Z.

Theorem uniqueProduct_spec_satisfied
    (arr : list Z)
    (h_precond : uniqueProduct_precond arr) :
  uniqueProduct_postcond
    arr (uniqueProduct arr h_precond) h_precond.
Admitted.
