(*
  Statement-only formalization of the Logipedia corpus artifact
  gcd.let_clause_1544 (catalog title "gcd.let_clause_1544"): an
  induction-style coefficient-existence hypothesis and the stated
  natural-number premises imply that commuting the final product preserves
  its truncated-difference equality with the fuel-indexed auxiliary gcd.
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

val gcd_let_clause_1544 =
  ``!(p : num) (q : num).
      (!(m : num) (n : num).
         0 < n ==>
         n <= m ==>
         n <= q ==>
         ?(a : num) (b : num).
           a * n - b * m = logipedia_gcd_gcd_aux q m n \/
           b * m - a * n = logipedia_gcd_gcd_aux q m n)
      ==>
      !(m : num) (n : num).
        0 < n ==>
        n <= m ==>
        n <= SUC q ==>
        ~divides n m ==>
        !a : num.
          (?(b : num).
             a * (m MOD n) - b * n =
               logipedia_gcd_gcd_aux q n (m MOD n) \/
             b * n - a * (m MOD n) =
               logipedia_gcd_gcd_aux q n (m MOD n))
          ==>
          !b : num.
            (a * (m MOD n) - b * n =
               logipedia_gcd_gcd_aux q n (m MOD n) \/
             b * n - a * (m MOD n) =
               logipedia_gcd_gcd_aux q n (m MOD n))
            ==>
            a * (m MOD n) - b * n =
              logipedia_gcd_gcd_aux q n (m MOD n)
            ==>
            a * (m MOD n) - n * b =
              logipedia_gcd_gcd_aux q n (m MOD n)``;
