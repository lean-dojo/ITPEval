(* Statement-only formalization of PutnamBench corpus artifact putnam_1993_a1:
   the value of a horizontal line for which two areas cut from the cubic
   y = 2x - 3x^3 are equal. This file contains no proof. *)

From Stdlib Require Import Reals RiemannInt.

Open Scope R_scope.

Definition putnam_1993_a1_solution : R := 4 / 9.

Definition putnam_1993_a1_left_integrand (x : R) : R :=
  Rmax 0 (putnam_1993_a1_solution - (2 * x - 3 * x ^ 3)).

Definition putnam_1993_a1_right_integrand (x : R) : R :=
  Rmax 0 ((2 * x - 3 * x ^ 3) - putnam_1993_a1_solution).

Theorem putnam_1993_a1 :
  0 < putnam_1993_a1_solution /\
  putnam_1993_a1_solution < 4 * sqrt 2 / 9 /\
  exists left_integrable :
      Riemann_integrable
        putnam_1993_a1_left_integrand 0 (sqrt 2 / 3),
    exists right_integrable :
        Riemann_integrable
          putnam_1993_a1_right_integrand 0 (sqrt 6 / 3),
      RiemannInt left_integrable = RiemannInt right_integrable.
Admitted.
