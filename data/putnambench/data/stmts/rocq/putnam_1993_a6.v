(* Statement-only formalization of PutnamBench artifact putnam_1993_a6:
   a self-describing sequence of 2s and 3s has its 2-valued positions
   represented by a real floor sequence. This file contains no proof. *)

From Stdlib Require Import Reals ZArith.

Fixpoint putnam_1993_a6_prefix_sum
    (seq : nat -> nat) (N : nat) : nat :=
  match N with
  | O => O
  | S N' => putnam_1993_a6_prefix_sum seq N' + (seq N' + 1)
  end.

Theorem putnam_1993_a6 :
  forall seq : nat -> nat,
    (forall n : nat, seq n = 2 \/ seq n = 3) ->
    (forall n : nat,
        seq n = 2 <->
        exists N : nat, n = putnam_1993_a6_prefix_sum seq N) ->
    exists r : R,
      forall n : nat,
        seq n = 2 <->
        exists m : nat,
          Z.of_nat (n + 1) = (1 + Zfloor (r * INR m))%Z.
Admitted.
