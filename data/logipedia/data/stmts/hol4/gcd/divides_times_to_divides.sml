(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_times_to_divides (catalog title
  "gcd.divides_times_to_divides"): for natural numbers p, n, and m, if p is
  prime and divides the product n * m, then p divides n or p divides m. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val gcd_divides_times_to_divides =
  ``!p n m : num.
      prime p ==>
      divides p (n * m) ==>
      divides p n \/ divides p m``;
