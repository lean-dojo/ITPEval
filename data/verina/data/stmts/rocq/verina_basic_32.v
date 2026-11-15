(* Statement-only formalization of VERINA corpus artifact verina_basic_32,
   catalog title "swapFirstAndLast": an executable swap of the first and last
   elements of a nonempty integer array, together with its size, endpoint,
   unchanged-middle postcondition and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition swapFirstAndLast_precond (a : list Z) : Prop :=
  (0 < length a)%nat.

Fixpoint swapFirstAndLast_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' =>
          x :: swapFirstAndLast_set_nth index' value rest
      end
  end.

Definition swapFirstAndLast
    (a : list Z)
    (_h_precond : swapFirstAndLast_precond a) : list Z :=
  let first := nth 0%nat a 0%Z in
  let last := nth (length a - 1)%nat a 0%Z in
  let with_first_replaced :=
    swapFirstAndLast_set_nth 0%nat last a in
  swapFirstAndLast_set_nth
    (length a - 1)%nat first with_first_replaced.

Definition swapFirstAndLast_postcond
    (a result : list Z)
    (_h_precond : swapFirstAndLast_precond a) : Prop :=
  length result = length a /\
  nth 0%nat result 0%Z =
    nth (length a - 1)%nat a 0%Z /\
  nth (length result - 1)%nat result 0%Z =
    nth 0%nat a 0%Z /\
  forallb
    (fun i =>
      Z.eqb
        (nth (i + 1)%nat result 0%Z)
        (nth (i + 1)%nat a 0%Z))
    (seq 0%nat (length result - 2)%nat) = true.

Theorem swapFirstAndLast_spec_satisfied
    (a : list Z)
    (h_precond : swapFirstAndLast_precond a) :
  swapFirstAndLast_postcond
    a (swapFirstAndLast a h_precond) h_precond.
Admitted.
