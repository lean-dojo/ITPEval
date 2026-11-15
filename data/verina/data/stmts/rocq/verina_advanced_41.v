(* Statement-only formalization of VERINA corpus artifact verina_advanced_41,
   catalog title "maxOfThree": an executable conditional computation of the
   maximum of three integers, together with its upper-bound and input-membership
   correctness contract. This file contains no proof. *)

From Stdlib Require Import Bool.Bool ZArith.

Definition maxOfThree_precond (_a _b _c : Z) : Prop :=
  True.

Definition maxOfThree
    (a b c : Z)
    (_h_precond : maxOfThree_precond a b c) : Z :=
  if andb (Z.geb a b) (Z.geb a c) then a
  else if andb (Z.geb b a) (Z.geb b c) then b
  else c.

Definition maxOfThree_postcond
    (a b c result : Z)
    (_h_precond : maxOfThree_precond a b c) : Prop :=
  ((a <= result)%Z /\ (b <= result)%Z /\ (c <= result)%Z) /\
  (result = a \/ result = b \/ result = c).

Theorem maxOfThree_spec_satisfied
    (a b c : Z)
    (h_precond : maxOfThree_precond a b c) :
  maxOfThree_postcond
    a b c (maxOfThree a b c h_precond) h_precond.
Admitted.
