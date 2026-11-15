(* Statement-only formalization of VERINA corpus artifact verina_basic_76,
   catalog title "myMin": an executable comparison returning the minimum of
   two integers, together with its trivial precondition, branch postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition myMin_precond (_x _y : Z) : Prop :=
  True.

Definition myMin
    (x y : Z)
    (_h_precond : myMin_precond x y) : Z :=
  if Z.ltb x y then x else y.

Definition myMin_postcond
    (x y result : Z)
    (_h_precond : myMin_precond x y) : Prop :=
  (x <= y -> result = x) /\
  (x > y -> result = y).

Theorem myMin_spec_satisfied
    (x y : Z)
    (h_precond : myMin_precond x y) :
  myMin_postcond x y (myMin x y h_precond) h_precond.
Admitted.
