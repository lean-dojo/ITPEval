(* Statement-only formalization of VERINA corpus artifact verina_basic_100,
   catalog title "Triple": an executable integer function that returns three
   times its input, together with its correctness contract. This file
   contains no proof. *)

From Stdlib Require Import ZArith.

Open Scope Z_scope.

Definition Triple_precond (_x : Z) : Prop :=
  True.

Definition Triple
    (x : Z)
    (_h_precond : Triple_precond x) : Z :=
  if Z.eqb x 0 then
    0
  else
    let y := 2 * x in
    x + y.

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
