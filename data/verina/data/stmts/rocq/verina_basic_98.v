(* Statement-only formalization of VERINA corpus artifact verina_basic_98
   (verina__rocq__verina_basic_98), catalog title "Triple": an executable
   integer function that multiplies its input by three, together with its
   unconditional precondition, postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition Triple_precond (_x : Z) : Prop :=
  True.

Definition Triple
    (x : Z)
    (_h_precond : Triple_precond x) : Z :=
  x * 3.

Definition Triple_postcond
    (x : Z)
    (result : Z)
    (_h_precond : Triple_precond x) : Prop :=
  Z.div result 3 = x /\
  Z.div result 3 * 3 = result.

Theorem Triple_spec_satisfied
    (x : Z)
    (h_precond : Triple_precond x) :
  Triple_postcond x (Triple x h_precond) h_precond.
Admitted.
