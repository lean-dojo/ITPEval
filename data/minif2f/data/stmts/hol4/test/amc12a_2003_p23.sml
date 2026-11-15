(*
  Statement-only formalization of miniF2F test problem amc12a_2003_p23: counting the positive
  natural numbers whose squares divide the product of 1! through 9!. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val amc12a_2003_p23 =
  ``FINITE
      {k : num |
         0 < k /\
         divides (k * k) (PROD_IMAGE FACT (count 10 DELETE 0))}
    ==>
    CARD
      {k : num |
         0 < k /\
         divides (k * k) (PROD_IMAGE FACT (count 10 DELETE 0))} =
      672``;
