(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_to_gcd_aux (catalog title "gcd.divides_to_gcd_aux"): for
  natural numbers p, m, and n, if p and n are positive and n divides m,
  then the fuel-indexed auxiliary Euclidean gcd at p, m, and n equals n.
  This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory dividesTheory;

val logipedia_gcd_gcd_aux_def = Define `
  (logipedia_gcd_gcd_aux 0 (m : num) (n : num) = m) /\
  (logipedia_gcd_gcd_aux (SUC p) m n =
    if m MOD n = 0 then
      n
    else
      logipedia_gcd_gcd_aux p n (m MOD n))
`;

val gcd_divides_to_gcd_aux =
  ``!(p : num) (m : num) (n : num).
      0 < p ==>
      0 < n ==>
      divides n m ==>
      logipedia_gcd_gcd_aux p m n = n``;
