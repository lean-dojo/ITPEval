(* Statement-only formalization of VERINA corpus artifact verina_basic_101,
   catalog title "Triple": an executable integer function that doubles its
   input and then adds the original input, together with its correctness
   contract. This file contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition Triple_precond (_x : Z) : Prop :=
  True.

Definition Triple
    (x : Z)
    (_h_precond : Triple_precond x) : Z :=
  let y := x * 2 in
  y + x.

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
