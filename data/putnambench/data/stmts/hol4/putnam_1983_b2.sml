(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1983_b2:
  existence of a real polynomial whose integer floor on every positive
  natural counts representations as sums of powers of two, with each power
  used at most three times. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory polyTheory;
open pred_setTheory bagTheory;

val putnam_1983_b2 =
  ``let representations =
      \n : num.
        {M : num bag |
           FINITE_BAG M /\
           (!m : num.
              BAG_IN m M ==> ?k : num. m = 2 ** k) /\
           (!m : num.
              BAG_IN m M ==> M m <= 3) /\
           BAG_GEN_SUM M 0 = n}
    in
    let f =
      \n : num. CARD (representations n)
    in
    let putnam_1983_b2_solution = T
    in
      ((?p : real list.
          !n : num.
            0 < n
            ==>
            INT_FLOOR (poly p (&n)) = int_of_num (f n))
       <=>
       putnam_1983_b2_solution)``;
