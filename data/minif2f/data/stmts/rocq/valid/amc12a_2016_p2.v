Require Import Reals.

Open Scope R_scope.

(* The exponent is real, as in the original exponential equation. *)
Theorem amc12a_2016_p2 :
  forall x : R,
    Rpower 10 x * Rpower 100 (2 * x) = 1000 ^ 5 ->
    x = 3.

Proof.
