(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1979_a1:
  the product-maximizing nonempty multiset of positive natural numbers whose
  sum is 1979. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory bagTheory containerTheory;

val putnam_1979_a1 =
  ``let solution : num bag =
      BAG_INSERT 2 (LIST_TO_BAG (REPLICATE 659 3))
    in
      !P : num bag -> bool.
        (!A : num bag.
           P A <=>
           FINITE_BAG A /\
           BAG_CARD A > 0 /\
           (!i : num. BAG_IN i A ==> i > 0) /\
           BAG_GEN_SUM A 0 = 1979)
        ==>
        P solution /\
        !A : num bag.
          P A ==> BAG_GEN_PROD solution 1 >= BAG_GEN_PROD A 1``;
