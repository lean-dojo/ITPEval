(* Statement-only formalization of Hundred Theorems item 070,
   "The Perfect Number Theorem". This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition multiplicative (f : nat -> nat) :=
  forall a b, coprime a b -> f (a * b) = f a * f b.

Definition dirichlet_conv (f g : nat -> nat) n :=
  if n > 0
  then \sum_(d <- divisors n) f d * g (n %/ d)
  else 0.

Definition sigma := dirichlet_conv (fun n => n) (fun _ => 1).
Definition perfect p := sigma p = 2 * p.

(* Euclid's direction: every Mersenne prime yields an even perfect number. *)
Theorem EuclidT p :
  prime (2 ^ p - 1) ->
  perfect (2 ^ (p - 1) * (2 ^ p - 1)).
Proof.
Admitted.

(* Euler's converse: every positive even perfect number has Euclid's form. *)
Theorem EulerT p :
  perfect p ->
  2 %| p ->
  p > 0 ->
  exists n,
    p = (2 ^ n - 1) * 2 ^ n.-1 /\
    prime (2 ^ n - 1).
Proof.
Admitted.
