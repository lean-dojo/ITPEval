(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_a2:
  for each n at least 2, the largest possible number of negative coefficients
  in the square of a real polynomial of degree n is 2n - 2. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory;

val putnam_2022_a2 =
  ``!n : num.
      2 <= n
      ==>
      let degree_n =
        \p : num -> real.
          p n <> 0 /\
          !k : num. n < k ==> p k = 0
      in
      let square_coeff =
        \p : num -> real.
        \k : num.
          SIGMA
            (\i : num. p i * p (k - i))
            (count (k + 1))
      in
      let negative_count =
        \p : num -> real.
          CARD
            {k : num |
               k <= 2 * n /\
               square_coeff p k < 0}
      in
        (!p : num -> real.
           degree_n p
           ==>
           negative_count p <= 2 * n - 2) /\
        ?p : num -> real.
          degree_n p /\
          negative_count p = 2 * n - 2``;
