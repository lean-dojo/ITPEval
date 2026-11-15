(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_a5:
  the polynomials with coefficients 1 through n are relatively prime for
  distinct positive indices. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory realTheory polyTheory;

val putnam_2014_a5 =
  ``let P =
      \n : num.
        GENLIST (\i : num. &(i + 1) : real) n
    in
      !j k : num.
        0 < j /\ 0 < k /\ j <> k
        ==>
        ?a b : real list.
          !x : real.
            poly a x * poly (P j) x +
            poly b x * poly (P k) x =
            1``;
