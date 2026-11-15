(* Statement-only formalization of VERINA corpus artifact verina_basic_50,
   catalog title "Abs": executable integer absolute value by a sign test,
   together with its unrestricted precondition, branchwise postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition Abs_precond (_x : Z) : Prop :=
  True.

Definition Abs
    (x : Z)
    (_h_precond : Abs_precond x) : Z :=
  if Z.ltb x 0%Z then -x else x.

Definition Abs_postcond
    (x : Z)
    (result : Z)
    (_h_precond : Abs_precond x) : Prop :=
  (0%Z <= x -> x = result) /\
  (x < 0%Z -> x + result = 0%Z).

Theorem Abs_spec_satisfied
    (x : Z)
    (h_precond : Abs_precond x) :
  Abs_postcond x (Abs x h_precond) h_precond.
Admitted.
