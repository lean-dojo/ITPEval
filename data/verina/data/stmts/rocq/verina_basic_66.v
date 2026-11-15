(* Statement-only formalization of VERINA corpus artifact verina_basic_66,
   catalog title "ComputeIsEven": an executable Boolean test determining
   whether any integer is twice another integer, together with its trivial
   precondition, exact evenness postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Open Scope Z_scope.

Definition ComputeIsEven_precond (_x : Z) : Prop :=
  True.

Definition ComputeIsEven
    (x : Z)
    (_h_precond : ComputeIsEven_precond x) : bool :=
  Z.eqb (Z.modulo x 2) 0.

Definition ComputeIsEven_postcond
    (x : Z)
    (result : bool)
    (_h_precond : ComputeIsEven_precond x) : Prop :=
  result = true <-> exists k : Z, x = 2 * k.

Theorem ComputeIsEven_spec_satisfied
    (x : Z)
    (h_precond : ComputeIsEven_precond x) :
  ComputeIsEven_postcond
    x (ComputeIsEven x h_precond) h_precond.
Admitted.
