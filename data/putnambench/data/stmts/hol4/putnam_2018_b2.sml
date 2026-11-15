(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2018_b2:
  the polynomial with coefficients n, n-1, ..., 1 has no complex root in
  the closed unit disk when n is positive. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory complexTheory;

val putnam_2018_b2 =
  ``!n : num.
      0 < n
      ==>
      let f_n =
        \z : complex.
          ITSET
            (\k acc.
               complex_of_real (&(n - k)) * z pow k + acc)
            (count n)
            (0 : complex)
      in
        !z : complex.
          modu z <= 1
          ==>
          f_n z <> 0``;
