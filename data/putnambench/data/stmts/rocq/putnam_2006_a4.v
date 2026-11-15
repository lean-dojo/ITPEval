(* Statement-only formalization of PutnamBench artifact putnam_2006_a4:
   the average number of endpoint-aware local maxima among permutations of
   an n-element set. This file contains no proof. *)

From Stdlib Require Import Reals.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition putnam_2006_a4_is_permutation {n : nat}
    (p : {ffun 'I_n -> 'I_n}) : bool :=
  [forall i : 'I_n,
    [forall j : 'I_n, (p i == p j) ==> (i == j)]].

Definition putnam_2006_a4_permutation_value {n : nat}
    (p : {ffun 'I_n -> 'I_n}) (i : nat) : nat :=
  match insub i with
  | Some k => nat_of_ord (p k)
  | None => 0
  end.

Definition putnam_2006_a4_is_local_maximum {n : nat}
    (p : {ffun 'I_n -> 'I_n}) (k : 'I_n) : bool :=
  ((nat_of_ord k == 0) ||
   (putnam_2006_a4_permutation_value p (nat_of_ord k - 1) <
    putnam_2006_a4_permutation_value p (nat_of_ord k))) &&
  ((nat_of_ord k == n - 1) ||
   (putnam_2006_a4_permutation_value p (nat_of_ord k) >
    putnam_2006_a4_permutation_value p (nat_of_ord k + 1))).

Definition putnam_2006_a4_local_maximum_count {n : nat}
    (p : {ffun 'I_n -> 'I_n}) : nat :=
  \sum_(k : 'I_n)
    (if putnam_2006_a4_is_local_maximum p k then 1 else 0).

Definition putnam_2006_a4_solution (n : nat) : R :=
  (INR n + 1) / 3.

Theorem putnam_2006_a4 (n : nat) (hn : (1 < n)%nat) :
  Rdiv
    (INR (\sum_(p : {ffun 'I_n -> 'I_n} |
                   putnam_2006_a4_is_permutation p)
           putnam_2006_a4_local_maximum_count p))
    (INR
      (#|[pred p : {ffun 'I_n -> 'I_n} |
           putnam_2006_a4_is_permutation p]|)) =
  putnam_2006_a4_solution n.
Admitted.
