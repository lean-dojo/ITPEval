Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Open Scope nat_scope.

Theorem mathd_numbertheory_296:
  forall n : nat,
  2 <= n ->
  (* The cube and fourth-power conditions are independent hypotheses. *)
  (exists x : nat, x^3 = n) ->
  (exists t : nat, t^4 = n) ->
  4096 <= n.
Proof.
Admitted.
