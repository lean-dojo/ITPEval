(* Statement-only formalization of PutnamBench corpus artifact putnam_2014_b1:
   positive integers with a unique base-10 over-expansion are exactly those
   whose ordinary decimal expansion contains no zero digit; this file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Ensembles.

Fixpoint putnam_2014_b1_value (digits : list nat) : nat :=
  match digits with
  | nil => 0
  | digit :: remaining =>
      digit + 10 * putnam_2014_b1_value remaining
  end.

Definition putnam_2014_b1_overexpansion
    (N : nat) (digits : list nat) : Prop :=
  putnam_2014_b1_value digits = N /\
  last digits 0 <> 0 /\
  Forall (fun digit : nat => (digit <= 10)%nat) digits.

Definition putnam_2014_b1_solution : Ensemble nat :=
  fun N : nat =>
    (0 < N)%nat /\
    forall k : nat,
      (0 < Nat.div N (Nat.pow 10 k))%nat ->
      Nat.modulo (Nat.div N (Nat.pow 10 k)) 10 <> 0.

Theorem putnam_2014_b1
    (S : Ensemble nat)
    (hS :
      forall N : nat,
        In nat S N <->
        (0 < N)%nat /\
        exists digits : list nat,
          putnam_2014_b1_overexpansion N digits /\
          forall other : list nat,
            putnam_2014_b1_overexpansion N other ->
            other = digits) :
  S = putnam_2014_b1_solution.
Admitted.
