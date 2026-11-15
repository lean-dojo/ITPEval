(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b6:
  the alternating series whose coefficients count odd divisors of each
  positive integer below the square root of twice that integer converges to
  pi squared divided by 16. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory realTheory;
open real_sigmaTheory seqTheory transcTheory;

val putnam_2015_b6 =
  ``!A : num -> num.
      (!k : num.
         0 < k
         ==>
         A k =
           CARD
             {j : num |
                ODD j /\
                divides j k /\
                (&j : real) < sqrt (2 * &k)})
      ==>
      ((((\K : num.
            SIGMA
              (\n : num.
                 (~1 : real) pow n * &(A (n + 1)) / &(n + 1))
              (count K)) : num -> real) -->
        (pi pow 2 / 16 : real))
       sequentially)``;
