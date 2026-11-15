(* Statement-only formalization of VERINA corpus artifact verina_basic_55,
   catalog title "Compare": an executable Boolean equality test for two
   integers, together with its trivial precondition, two-branch postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Open Scope Z_scope.

Definition Compare_precond (_a _b : Z) : Prop :=
  True.

Definition Compare
    (a b : Z)
    (_h_precond : Compare_precond a b) : bool :=
  if Z.eqb a b then true else false.

Definition Compare_postcond
    (a b : Z)
    (result : bool)
    (_h_precond : Compare_precond a b) : Prop :=
  (a = b -> result = true) /\
  (a <> b -> result = false).

Theorem Compare_spec_satisfied
    (a b : Z)
    (h_precond : Compare_precond a b) :
  Compare_postcond a b (Compare a b h_precond) h_precond.
Admitted.
