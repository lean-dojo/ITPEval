(* Statement-only formalization of VERINA corpus artifact verina_basic_8,
   catalog title "myMin": an executable comparison returning the minimum of
   two integers, together with its trivial precondition, minimum postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition myMin_precond (_a _b : Z) : Prop :=
  True.

Definition myMin
    (a b : Z)
    (_h_precond : myMin_precond a b) : Z :=
  if Z.leb a b then a else b.

Definition myMin_postcond
    (a b result : Z)
    (_h_precond : myMin_precond a b) : Prop :=
  (result <= a /\ result <= b) /\
  (result = a \/ result = b).

Theorem myMin_spec_satisfied
    (a b : Z)
    (h_precond : myMin_precond a b) :
  myMin_postcond a b (myMin a b h_precond) h_precond.
Admitted.
