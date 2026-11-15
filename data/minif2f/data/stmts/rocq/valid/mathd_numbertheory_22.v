Require Import Arith.
Require Import Nat.

Theorem mathd_numbertheory_22 :
  forall b : nat,
  b < 10 ->
  (* Perfect-squareness is a complete hypothesis. *)
  (exists a : nat, (10 * b + 6) = a * a) ->
  (b = 3 \/ b = 1).
Proof.
Admitted.
