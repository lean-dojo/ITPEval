(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.match_divides_prop (catalog title "primes.match_divides_prop"): a
  continuation that yields an arbitrary proposition from every quotient
  witness for n dividing m eliminates the natural-number divisibility
  proposition. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_match_divides_prop =
  ``!(n : num) (m : num) (return_ : bool).
      (!q : num. m = n * q ==> return_) ==>
      divides n m ==>
      return_``;
