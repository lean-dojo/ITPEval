(* Statement-only formalization of PutnamBench artifact putnam_1986_b1:
   the positive rectangle height determined by the unit-circle dimension and
   equal-area equations is 2/5. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Definition putnam_1986_b1_solution : R := 2 / 5.

Theorem putnam_1986_b1
    (b h : R)
    (hbh : b > 0 /\ h > 0 /\ b ^ 2 + h ^ 2 = 2 ^ 2)
    (areaeq : b * h = (1 / 2) * b * (1 - h / 2)) :
  h = putnam_1986_b1_solution.
Admitted.
