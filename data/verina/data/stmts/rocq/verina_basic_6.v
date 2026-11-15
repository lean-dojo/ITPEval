(* Statement-only formalization of VERINA corpus artifact verina_basic_6,
   catalog title "minOfThree": executable selection of the minimum of three
   integers, together with its trivial precondition, minimum postcondition,
   and final correctness proposition. This file contains no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Open Scope Z_scope.

Definition minOfThree_precond (_a _b _c : Z) : Prop :=
  True.

Definition minOfThree
    (a b c : Z)
    (_h_precond : minOfThree_precond a b c) : Z :=
  if andb (Z.leb a b) (Z.leb a c) then
    a
  else if andb (Z.leb b a) (Z.leb b c) then
    b
  else
    c.

Definition minOfThree_postcond
    (a b c result : Z)
    (_h_precond : minOfThree_precond a b c) : Prop :=
  (result <= a /\ result <= b /\ result <= c) /\
  (result = a \/ result = b \/ result = c).

Theorem minOfThree_spec_satisfied
    (a b c : Z)
    (h_precond : minOfThree_precond a b c) :
  minOfThree_postcond
    a b c (minOfThree a b c h_precond) h_precond.
Admitted.
