(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2007_b6:
  the number of unordered collections of factorial-denomination coins making
  n factorial satisfies the stated two-sided asymptotic bounds for one
  constant independent of n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory bagTheory;

val putnam_2007_b6 =
  ``let f =
      \n : num.
        CARD
          {M : num bag |
             FINITE_BAG M /\
             BAG_GEN_SUM M 0 = FACT n /\
             !m : num.
               BAG_IN m M
               ==>
               ?k : num. 1 <= k /\ k <= n /\ m = FACT k}
    in
      ?C : real.
        !n : num.
          2 <= n
          ==>
          ((&n : real) powr
             (((&n : real) pow 2) / 2 - C * (&n : real)) *
             exp (-(((&n : real) pow 2) / 4)) <=
             (&(f n) : real)) /\
          ((&(f n) : real) <=
             (&n : real) powr
               (((&n : real) pow 2) / 2 + C * (&n : real)) *
               exp (-(((&n : real) pow 2) / 4)))``;
