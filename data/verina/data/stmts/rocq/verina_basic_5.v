(* Statement-only formalization of VERINA corpus artifact verina_basic_5,
   catalog title "multiply": executable multiplication of two integers,
   together with its trivial precondition, two-sided zero-difference
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition multiply_precond (_a _b : Z) : Prop :=
  True.

Definition multiply
    (a b : Z)
    (_h_precond : multiply_precond a b) : Z :=
  a * b.

Definition multiply_postcond
    (a b result : Z)
    (_h_precond : multiply_precond a b) : Prop :=
  result - a * b = 0 /\ a * b - result = 0.

Theorem multiply_spec_satisfied
    (a b : Z)
    (h_precond : multiply_precond a b) :
  multiply_postcond a b (multiply a b h_precond) h_precond.
Admitted.
