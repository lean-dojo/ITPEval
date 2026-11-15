(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_aux_mn (catalog title "gcd.divides_gcd_aux_mn"): for
  natural numbers p, m, and positive n with n at most both m and p,
  gcd_aux p m n divides both m and n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_gcd_auxiliary_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_gcd_gcd_aux",
  logipedia_gcd_auxiliary_type);

val gcd_divides_gcd_aux_mn =
  ``!p : num.
      !m : num.
        !n : num.
          0 < n ==>
          n <= m ==>
          n <= p ==>
          divides (logipedia_gcd_gcd_aux p m n) m /\
          divides (logipedia_gcd_gcd_aux p m n) n``;
