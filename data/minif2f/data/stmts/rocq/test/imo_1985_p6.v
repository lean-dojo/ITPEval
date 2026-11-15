Require Import Reals.
Open Scope R_scope.

(*
  Statement-only formalization of miniF2F test problem imo_1985_p6:
  exactly one initial value keeps the positive-index recurrence increasing
  below one.
*)

Theorem imo_1985_p6 :
  forall (f : nat -> R -> R),
  (forall x : R, f 1%nat x = x) ->
  (forall (x : R) (n : nat), (0 < n)%nat ->
    f (S n) x = f n x * (f n x + /INR n)) ->
  exists! a : R, forall n : nat,
    (0 < n)%nat ->
    0 < f n a /\ f n a < f (S n) a /\ f (S n) a < 1.

Proof.
