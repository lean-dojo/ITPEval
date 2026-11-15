(*
  Statement-only formalization of Logipedia corpus artifact gcd.eq_minus_gcd
  (catalog title "gcd.eq_minus_gcd"): for any two natural numbers, there are
  natural coefficients such that one of the two truncated differences of
  their corresponding multiples equals their greatest common divisor. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem eq_minus_gcd :
  forall m n : nat,
    exists a b : nat,
      a * n - b * m = Nat.gcd n m \/
      b * m - a * n = Nat.gcd n m.
Admitted.
