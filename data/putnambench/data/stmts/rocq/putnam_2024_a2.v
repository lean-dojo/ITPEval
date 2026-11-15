(* Statement-only formalization of PutnamBench corpus artifact putnam_2024_a2:
   the classification of real polynomials satisfying a composition and
   divisibility identity. This file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Fixpoint putnam_2024_a2_polynomial_eval
    (coefficients : list R) (x : R) : R :=
  match coefficients with
  | nil => 0
  | coefficient :: remaining =>
      coefficient +
      x * putnam_2024_a2_polynomial_eval remaining x
  end.

Theorem putnam_2024_a2 :
  forall p : list R,
    (exists q : list R,
      forall x : R,
        putnam_2024_a2_polynomial_eval
          p (putnam_2024_a2_polynomial_eval p x) - x =
        (putnam_2024_a2_polynomial_eval p x - x) ^ 2 *
          putnam_2024_a2_polynomial_eval q x) <->
    exists a : R,
      (forall x : R,
        putnam_2024_a2_polynomial_eval p x = x + a) \/
      (forall x : R,
        putnam_2024_a2_polynomial_eval p x = - x + a).
Admitted.
