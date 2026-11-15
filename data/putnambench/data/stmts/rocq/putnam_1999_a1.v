(* Statement-only formalization of PutnamBench corpus artifact putnam_1999_a1:
   existence of three real polynomials whose absolute-value combination equals
   a specified piecewise linear function; this file contains no proof. *)

From Stdlib Require Import Reals List.

Open Scope R_scope.

Definition putnam_1999_a1_polynomial : Type := list R.

Fixpoint putnam_1999_a1_eval
    (p : putnam_1999_a1_polynomial) (x : R) : R :=
  match p with
  | nil => 0
  | coefficient :: remaining =>
      coefficient + x * putnam_1999_a1_eval remaining x
  end.

Definition putnam_1999_a1_solution : Prop := True.

Theorem putnam_1999_a1 :
  putnam_1999_a1_solution <->
  exists f g h : putnam_1999_a1_polynomial,
    forall x : R,
      Rabs (putnam_1999_a1_eval f x) -
      Rabs (putnam_1999_a1_eval g x) +
      putnam_1999_a1_eval h x =
      if Rlt_dec x (-1) then
        -1
      else if Rle_dec x 0 then
        3 * x + 2
      else
        -2 * x + 2.
Admitted.
