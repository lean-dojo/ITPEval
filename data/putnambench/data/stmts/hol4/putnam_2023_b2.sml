(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b2:
  the minimum number of ones in the binary expansion of a positive multiple
  of 2023 is 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_2023_b2 =
  ``!ones : num -> num.
      ones 0 = 0 /\
      (!m : num.
         0 < m
         ==>
         ones m =
           (if m MOD 2 = 1 then 1 else 0) + ones (m DIV 2))
      ==>
      (!n : num.
         0 < n
         ==>
         3 <= ones (2023 * n)) /\
      (?n : num.
         0 < n /\
         ones (2023 * n) = 3)``;
