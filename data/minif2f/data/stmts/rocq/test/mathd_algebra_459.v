Require Import QArith.
Require Import ZArith.

Open Scope Q_scope.

(*
  Statement-only formalization of miniF2F test problem mathd_algebra_459:
  the reduced numerator and denominator of d sum to 28.
*)

Theorem mathd_algebra_459 :
  forall (a b c d : Q),
    3 * a == b + c + d ->
    4 * b == a + c + d ->
    2 * c == a + b + d ->
    8 * a + 10 * b + 6 * c == 24 ->
    (Qnum (Qred d) + Z.pos (Qden (Qred d)))%Z = 28%Z.

Proof.
