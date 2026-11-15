Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* A list with no duplicates is the native finite-set representation. *)
Theorem mathd_numbertheory_35 :
  forall S : list nat,
    NoDup S ->
    (forall n : nat, In n S <-> Nat.divide n (Nat.sqrt 196)) ->
    fold_right Nat.add 0 S = 24.
Proof.
Admitted.
