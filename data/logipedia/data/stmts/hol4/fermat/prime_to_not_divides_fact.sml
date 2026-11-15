(*
  Statement-only formalization of the Logipedia corpus artifact
  fermat.prime_to_not_divides_fact (catalog title
  "fermat.prime_to_not_divides_fact"): for natural numbers p and n, if p is
  prime and n is less than p, then p does not divide n factorial. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val fermat_prime_to_not_divides_fact =
  ``!p : num.
      prime p ==>
      !n : num.
        n < p ==>
        ~divides p (FACT n)``;
