(* Statement-only formalization of PutnamBench artifact putnam_1969_b1:
   divisibility by 24 of the sum of the positive divisors of a positive
   integer whose successor is divisible by 24. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope nat_scope.

Theorem putnam_1969_b1
    (n : nat)
    (hnpos : (0 < n)%nat)
    (hn : Nat.divide 24 (n + 1)) :
  Nat.divide 24 (\sum_(d <- divisors n) d).
Admitted.
