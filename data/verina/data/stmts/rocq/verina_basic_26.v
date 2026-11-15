(* Statement-only formalization of VERINA corpus artifact verina_basic_26,
   catalog title "isEven": an executable Boolean test deciding whether any
   integer has remainder zero modulo 2, together with its trivial precondition,
   parity postcondition, and final correctness proposition. This file contains
   no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Open Scope Z_scope.

Definition isEven_precond (_n : Z) : Prop :=
  True.

Definition isEven
    (n : Z)
    (_h_precond : isEven_precond n) : bool :=
  Z.eqb (Z.modulo n 2) 0.

Definition isEven_postcond
    (n : Z)
    (result : bool)
    (_h_precond : isEven_precond n) : Prop :=
  (Is_true result -> Z.modulo n 2 = 0) /\
  (~ Is_true result -> Z.modulo n 2 <> 0).

Theorem isEven_spec_satisfied
    (n : Z)
    (h_precond : isEven_precond n) :
  isEven_postcond n (isEven n h_precond) h_precond.
Admitted.
