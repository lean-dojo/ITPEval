Require Import Reals.
Require Import Sets.Ensembles.
Require Import Sets.Image.

Open Scope R_scope.

Theorem amc12a_2003_p25 :
  forall (a b : R) (f : R -> R),
    b > 0 ->
    (forall x : R, f x = sqrt (a * x^2 + b * x)) ->
    (* The source and image are both restricted by the square root's
       radicand, rather than by the always-nonnegative Coq square root. *)
    (forall x : R,
      0 <= a * x^2 + b * x <->
      exists z : R, 0 <= a * z^2 + b * z /\ f z = x) ->
    a = 0 \/ a = -4.

Proof.
