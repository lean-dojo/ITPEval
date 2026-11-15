(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1981_a1:
  the greatest exponent E(n) for which 5^E(n) divides the weighted factorial
  product 1^1 * 2^2 * ... * n^n has E(n) / n^2 tending to 1/8. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory;
open real_topologyTheory;

val putnam_1981_a1 =
  ``!E : num -> num.
      (!n : num.
         1 <= n
         ==>
         divides
           (5 EXP (E n))
           (PROD_IMAGE
              (\m : num. m EXP m)
              (IMAGE SUC (count n))) /\
         (!k : num.
            divides
              (5 EXP k)
              (PROD_IMAGE
                 (\m : num. m EXP m)
                 (IMAGE SUC (count n)))
            ==>
            k <= E n))
      ==>
      ((\n : num. &(E n) / (&n : real) pow 2) -->
       (1 / 8 : real))
      sequentially``;
