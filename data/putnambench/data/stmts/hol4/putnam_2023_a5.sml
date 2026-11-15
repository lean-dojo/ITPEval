(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a5:
  the complex zeros of a weighted power sum whose weights count ones in
  ternary expansions are exactly three specified values. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory complexTheory;

val putnam_2023_a5 =
  ``let num_ones =
      \k : num.
        SIGMA
          (\j : num.
             if (k DIV (3 ** j)) MOD 3 = 1 then 1 else 0)
          (count 1010)
    in
      let center =
        complex_of_real (-(&(3 ** 1010 - 1)) / 2)
      in
        let offset =
          (sqrt (&(9 ** 1010 - 1)) / 4) * i
        in
          {z : complex |
             ITSET
               (\k : num. \acc : complex.
                  (-2 : complex) pow (num_ones k) *
                    (z + complex_of_num k) pow 2023 +
                  acc)
               (count (3 ** 1010))
               0 =
             0} =
          {center; center + offset; center - offset}``;
