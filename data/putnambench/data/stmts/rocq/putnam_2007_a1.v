(* Statement-only formalization of PutnamBench corpus artifact putnam_2007_a1:
   the real parameters for which two reflected quadratic curves are
   tangent at an intersection; this file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_2007_a1_curve (alpha t : R) : R :=
  alpha * t ^ 2 + alpha * t + 1 / 24.

Definition putnam_2007_a1_tangent_parameter (alpha : R) : Prop :=
  exists x y : R,
    putnam_2007_a1_curve alpha x = y /\
    putnam_2007_a1_curve alpha y = x /\
    (2 * alpha * x + alpha) * (2 * alpha * y + alpha) = 1.

Definition putnam_2007_a1_solution (alpha : R) : Prop :=
  alpha = 2 / 3 \/
  alpha = 3 / 2 \/
  alpha = (13 + sqrt 601) / 12 \/
  alpha = (13 - sqrt 601) / 12.

Theorem putnam_2007_a1 :
  forall alpha : R,
    putnam_2007_a1_tangent_parameter alpha <->
    putnam_2007_a1_solution alpha.
Admitted.
