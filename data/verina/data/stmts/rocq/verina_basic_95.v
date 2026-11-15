(* Statement-only formalization of VERINA corpus artifact verina_basic_95,
   catalog title "swap": executable swapping of two nonnegative in-bounds
   indices of an integer array, together with its size, exchanged-entry,
   unchanged-other-entry postcondition and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition swap_precond
    (arr : list Z) (i j : Z) : Prop :=
  (0 <= i)%Z /\
  (0 <= j)%Z /\
  (Z.to_nat i < length arr)%nat /\
  (Z.to_nat j < length arr)%nat.

Fixpoint swap_set_nth
    (index : nat)
    (value : Z)
    (arr : list Z) : list Z :=
  match arr with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: swap_set_nth index' value rest
      end
  end.

Definition swap
    (arr : list Z)
    (i j : Z)
    (_h_precond : swap_precond arr i j) : list Z :=
  let i_nat := Z.to_nat i in
  let j_nat := Z.to_nat j in
  let arr1 :=
    swap_set_nth i_nat (nth j_nat arr 0%Z) arr in
  swap_set_nth j_nat (nth i_nat arr 0%Z) arr1.

Definition swap_postcond
    (arr : list Z)
    (i j : Z)
    (result : list Z)
    (_h_precond : swap_precond arr i j) : Prop :=
  length result = length arr /\
  nth (Z.to_nat i) result 0%Z =
    nth (Z.to_nat j) arr 0%Z /\
  nth (Z.to_nat j) result 0%Z =
    nth (Z.to_nat i) arr 0%Z /\
  forall k : nat,
    (k < length arr)%nat ->
    k <> Z.to_nat i ->
    k <> Z.to_nat j ->
    nth k result 0%Z = nth k arr 0%Z.

Theorem swap_spec_satisfied
    (arr : list Z)
    (i j : Z)
    (h_precond : swap_precond arr i j) :
  swap_postcond
    arr i j (swap arr i j h_precond) h_precond.
Admitted.
