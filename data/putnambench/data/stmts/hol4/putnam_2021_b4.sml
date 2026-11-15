(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b4:
  the remainder modulo a Fibonacci number of the product of k^k for positive
  k below that number is itself a Fibonacci number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2021_b4 =
  ``!F : num -> num.
      (F 0 = 0 /\
       F 1 = 1 /\
       (!n : num. F (n + 2) = F (n + 1) + F n))
      ==>
      !m : num.
        2 < m
        ==>
        ?p : num.
          PROD_IMAGE
            (\k : num. k EXP k)
            (IMAGE SUC (count (F m - 1))) MOD F m =
          F p``;
