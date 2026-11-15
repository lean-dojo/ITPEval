(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_b4:
  the sum of 2^a / (3^b 5^c) over positive integer triples that are side
  lengths of a triangle is the reduced rational number 17/21. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open real_topologyTheory;

val putnam_2015_b4 =
  ``let triangle_term =
      \(a : num) (b : num) (c : num).
        if 0 < a /\ 0 < b /\ 0 < c /\
           a < b + c /\ b < c + a /\ c < a + b
        then
          (2 : real) pow a /
            ((3 : real) pow b * (5 : real) pow c)
        else
          0
    in
      ((\N : num.
          SIGMA
            (\a : num.
               SIGMA
                 (\b : num.
                    SIGMA
                      (\c : num. triangle_term a b c)
                      (count N))
                 (count N))
            (count N)) -->
       (17 / 21 : real))
      sequentially``;
