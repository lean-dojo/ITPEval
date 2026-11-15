(* Statement-only formalization of PutnamBench corpus artifact putnam_1993_b6:
   a finite sequence of pairwise two-entry transformations sends three
   positive natural numbers to a state containing zero. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Inductive putnam_1993_b6_index : Type :=
| putnam_1993_b6_index0
| putnam_1993_b6_index1
| putnam_1993_b6_index2.

Definition putnam_1993_b6_state : Type :=
  putnam_1993_b6_index -> nat.

Definition putnam_1993_b6_state_equal
    (left right : putnam_1993_b6_state) : Prop :=
  forall i : putnam_1993_b6_index, left i = right i.

Theorem putnam_1993_b6
    (initial : putnam_1993_b6_state)
    (transform :
      putnam_1993_b6_index ->
      putnam_1993_b6_index ->
      putnam_1993_b6_state ->
      putnam_1993_b6_state)
    (initial_positive :
      forall i : putnam_1993_b6_index, (0 < initial i)%nat)
    (transform_rule :
      forall i j k : putnam_1993_b6_index,
        i <> j ->
        i <> k ->
        j <> k ->
        forall current : putnam_1993_b6_state,
          (((current i <= current j)%nat ->
            (transform i j current) i = (2 * current i)%nat /\
            (transform i j current) j = (current j - current i)%nat /\
            (transform i j current) k = current k) /\
           (~ ((current i <= current j)%nat) ->
            putnam_1993_b6_state_equal
              (transform i j current) current))) :
  exists (states : nat -> putnam_1993_b6_state) (N : nat),
    putnam_1993_b6_state_equal (states 0) initial /\
    (exists i : putnam_1993_b6_index, states N i = 0%nat) /\
    forall n : nat,
      (n < N)%nat ->
      exists i j : putnam_1993_b6_index,
        i <> j /\
        putnam_1993_b6_state_equal
          (transform i j (states n))
          (states (Nat.succ n)).
Admitted.
