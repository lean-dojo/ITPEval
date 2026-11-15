(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_b5:
  evaluation of a real infinite product as its parameter approaches 1 from
  below, with limit 2 / exp 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory
     real_topologyTheory transcTheory;

val putnam_2004_b5 =
  ``!xprod : real -> real.
      (!x : real.
         0 < x /\ x < 1
         ==>
         ((\N : num.
             REAL_PROD_IMAGE
               (\n : num.
                  ((1 + x pow (n + 1)) / (1 + x pow n)) powr
                    (x pow n))
               (count N)) -->
          xprod x)
           sequentially)
      ==>
      (xprod --> 2 / exp 1)
        (at 1 within {x : real | x < 1})``;
