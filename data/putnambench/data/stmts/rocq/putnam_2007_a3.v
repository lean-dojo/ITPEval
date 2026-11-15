(* Statement-only formalization of PutnamBench corpus artifact putnam_2007_a3:
   the probability that no prefix sum of a random ordering of the integers
   1 through 3k+1 is divisible by 3. This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint putnam_2007_a3_factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S m => S m * putnam_2007_a3_factorial m
  end.

Definition putnam_2007_a3_partial_sum {n : nat}
    (p : {ffun 'I_n -> 'I_n}) (j : 'I_n) : nat :=
  \sum_(i : 'I_n | i <= j) (nat_of_ord (p i) + 1).

Definition putnam_2007_a3_is_permutation {n : nat}
    (p : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i : 'I_n,
    [forall j : 'I_n, (p i == p j) ==> (i == j)]].

Definition putnam_2007_a3_good {n : nat}
    (p : {ffun 'I_n -> 'I_n}) : bool :=
  [forall j : 'I_n,
    putnam_2007_a3_partial_sum p j %% 3 != 0].

Definition putnam_2007_a3_good_count (n : nat) : nat :=
  #|[pred p : {ffun 'I_n -> 'I_n} |
      putnam_2007_a3_is_permutation p && putnam_2007_a3_good p]|.

Theorem putnam_2007_a3 :
  forall k : nat,
    (0 < k)%nat ->
    ((3 * k + 1) *
       putnam_2007_a3_factorial (2 * k) *
       putnam_2007_a3_good_count (3 * k + 1) =
     putnam_2007_a3_factorial k *
       putnam_2007_a3_factorial (k + 1) *
       putnam_2007_a3_factorial (3 * k + 1))%nat.
Admitted.
