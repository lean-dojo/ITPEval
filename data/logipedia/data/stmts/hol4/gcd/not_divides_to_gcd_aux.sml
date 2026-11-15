(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.not_divides_to_gcd_aux (catalog title "gcd.not_divides_to_gcd_aux"):
  for natural numbers p, m, and n, if n is positive and does not divide m,
  then one successor step of the fuel-indexed auxiliary Euclidean gcd reduces
  to the preceding step on n and m modulo n. This file contains no proof.
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

val gcd_not_divides_to_gcd_aux =
  ``!(p : num) (m : num) (n : num).
      0 < n ==>
      ~divides n m ==>
      logipedia_gcd_gcd_aux (SUC p) m n =
        logipedia_gcd_gcd_aux p n (m MOD n)``;
