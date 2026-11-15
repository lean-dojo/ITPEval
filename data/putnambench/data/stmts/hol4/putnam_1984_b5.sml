(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_b5:
  the alternating sum of m-th powers weighted by binary digit parity has base
  two, exponent m(m - 1)/2, and factorial argument m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory intrealTheory pred_setTheory realTheory
     transcTheory;

val putnam_1984_b5 =
  ``let solution =
      (((2 : int), (\x : real. x * (x - 1) / 2)), (\n : num. n))
    in
      let a = FST (FST solution) in
      let f = SND (FST solution) in
      let g = SND solution in
        !d : num -> num. !m : num.
          0 < m /\
          (!n : num.
             d n =
             if n < 2 then n
             else n MOD 2 + d (n DIV 2))
          ==>
          SIGMA
            (\k : num.
               (~1 : real) pow (d k) * &(k EXP m))
            (count (2 EXP m)) =
          (~1 : real) pow m *
            (real_of_int a) powr (f (&m)) *
            &(FACT (g m))``;
