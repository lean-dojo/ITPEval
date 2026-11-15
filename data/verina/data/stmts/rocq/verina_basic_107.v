(* Statement-only formalization of VERINA corpus artifact verina_basic_107,
   catalog title "ComputeAvg": the executable Euclidean integer average of
   two integers, together with its precondition, exact remainder-based
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition ComputeAvg_precond (_a _b : Z) : Prop :=
  True.

Definition ComputeAvg
    (a b : Z)
    (_h_precond : ComputeAvg_precond a b) : Z :=
  Z.div (a + b) 2.

Definition ComputeAvg_postcond
    (a b result : Z)
    (_h_precond : ComputeAvg_precond a b) : Prop :=
  2 * result = a + b - Z.modulo (a + b) 2.

Theorem ComputeAvg_spec_satisfied
    (a b : Z)
    (h_precond : ComputeAvg_precond a b) :
  ComputeAvg_postcond
    a b (ComputeAvg a b h_precond) h_precond.
Admitted.
