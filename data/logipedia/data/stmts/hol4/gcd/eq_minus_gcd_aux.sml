(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_minus_gcd_aux (catalog title "gcd.eq_minus_gcd_aux"): for natural
  numbers p, m, and positive n with n at most both m and p, there are natural
  coefficients such that one of the two truncated product differences equals
  the fuel-indexed auxiliary Euclidean gcd at p, m, and n. This file contains
  no proof.
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

val gcd_eq_minus_gcd_aux =
  ``!(p : num) (m : num) (n : num).
      0 < n ==>
      n <= m ==>
      n <= p ==>
      ?(a : num) (b : num).
        a * n - b * m = logipedia_gcd_gcd_aux p m n \/
        b * m - a * n = logipedia_gcd_gcd_aux p m n``;
