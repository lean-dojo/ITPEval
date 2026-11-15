(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b2:
  the attainable total costs of finite strictly rightward jump sequences from
  zero to one form the real interval (1/3, 1]. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2009_b2 =
  ``{c : real |
       ?s : num -> real.
         s 0 = 0 /\
         (!i j : num. i < j ==> s i < s j) /\
         ?n : num.
           s n = 1 /\
           SIGMA
             (\i : num.
                s (i + 1) pow 3 -
                s i * s (i + 1) pow 2)
             (count n) =
           c} =
    {c : real | 1 / 3 < c /\ c <= 1}``;
