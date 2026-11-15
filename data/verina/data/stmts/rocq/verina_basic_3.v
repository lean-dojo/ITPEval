(* Statement-only formalization of VERINA corpus artifact verina_basic_3,
   catalog title "isDivisibleBy11": an executable Boolean test deciding
   whether any integer is divisible by 11, together with its trivial
   precondition, two-sided divisibility postcondition, and final correctness
   proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Open Scope Z_scope.

Definition isDivisibleBy11_precond (_n : Z) : Prop :=
  True.

Definition isDivisibleBy11
    (n : Z)
    (_h_precond : isDivisibleBy11_precond n) : bool :=
  Z.eqb (Z.modulo n 11) 0.

Definition isDivisibleBy11_postcond
    (n : Z)
    (result : bool)
    (_h_precond : isDivisibleBy11_precond n) : Prop :=
  (Is_true result -> exists k : Z, n = 11 * k) /\
  (~ Is_true result -> forall k : Z, n <> 11 * k).

Theorem isDivisibleBy11_spec_satisfied
    (n : Z)
    (h_precond : isDivisibleBy11_precond n) :
  isDivisibleBy11_postcond
    n (isDivisibleBy11 n h_precond) h_precond.
Admitted.
