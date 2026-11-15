(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a3:
  the number of infinite nonzero-residue sequences satisfying a modular
  recurrence is congruent to zero or two modulo five. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2022_a3 =
  ``!p f : num.
      prime p /\
      5 < p /\
      f =
        CARD
          {a : num -> num |
             !n : num.
               0 < a n /\
               a n < p /\
               (a n * a (n + 2)) MOD p =
                 (1 + a (n + 1)) MOD p}
      ==>
      f MOD 5 = 0 \/ f MOD 5 = 2``;
