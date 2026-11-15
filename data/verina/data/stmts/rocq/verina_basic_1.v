(* Statement-only formalization of VERINA corpus artifact verina_basic_1,
   catalog title "hasOppositeSign": an executable Boolean test for whether
   two integers have strictly opposite signs, together with its correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Bool ZArith.

Open Scope Z_scope.

Definition hasOppositeSign_precond (_a _b : Z) : Prop :=
  True.

Definition hasOppositeSign
    (a b : Z)
    (_h_precond : hasOppositeSign_precond a b) : bool :=
  Z.ltb (a * b) 0.

Definition hasOppositeSign_postcond
    (a b : Z)
    (result : bool)
    (_h_precond : hasOppositeSign_precond a b) : Prop :=
  (((a < 0 /\ 0 < b) \/ (0 < a /\ b < 0)) ->
    result = true) /\
  (~ ((a < 0 /\ 0 < b) \/ (0 < a /\ b < 0)) ->
    result = false).

Theorem hasOppositeSign_spec_satisfied
    (a b : Z)
    (h_precond : hasOppositeSign_precond a b) :
  hasOppositeSign_postcond
    a b (hasOppositeSign a b h_precond) h_precond.
Admitted.
