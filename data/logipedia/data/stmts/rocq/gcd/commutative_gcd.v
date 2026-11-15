(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.commutative_gcd (catalog title "gcd.commutative_gcd"): the greatest
  common divisor of two natural numbers is unchanged when the arguments are
  exchanged. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem commutative_gcd :
  forall n m : nat,
    Nat.gcd n m = Nat.gcd m n.
Admitted.
