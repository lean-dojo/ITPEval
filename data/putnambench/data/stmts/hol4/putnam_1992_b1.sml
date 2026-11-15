(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b1:
  the minimum number of distinct pairwise averages determined by an
  n-element set of distinct real numbers is 2*n - 3. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_1992_b1 =
  ``!n : num.
      2 <= n
      ==>
      let averages =
        \S : real set.
          {x : real |
             ?a b : real.
               a IN S /\
               b IN S /\
               a <> b /\
               (a + b) / 2 = x}
      in
        (?S : real set.
           FINITE S /\
           CARD S = n /\
           FINITE (averages S) /\
           CARD (averages S) = 2 * n - 3) /\
        (!S : real set.
           FINITE S /\
           CARD S = n
           ==>
           FINITE (averages S) /\
           2 * n - 3 <= CARD (averages S))``;
