Require Import List.
Require Import Znumtheory.
Require Import ZArith.
Require Import Reals.
Require Import Lia.

Open Scope nat_scope.

(* The checked range starts at zero; omitting k = 0 and k = 1 changes
   the theorem and admits false small counterexamples. *)
Theorem imo_1987_p6 :
  forall (p : nat) (f : nat -> nat),
  (forall x, f x = x ^ 2 + x + p) ->
  (forall k, (INR k <= sqrt (INR p / 3))%R ->
    prime (Z.of_nat (f k))) ->
  forall i, i <= p - 2 -> prime (Z.of_nat (f i)).
Proof.
