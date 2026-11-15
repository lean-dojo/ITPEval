(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_b6:
  the number of ordered 64-tuples of distinct integers from 1 through 2017
  whose index-weighted sum is divisible by 2017. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory listTheory pred_setTheory;

val putnam_2017_b6 =
  ``CARD
      {xs : num list |
         LENGTH xs = 64 /\
         ALL_DISTINCT xs /\
         (!x : num. MEM x xs ==> 1 <= x /\ x <= 2017) /\
         divides 2017
           (SIGMA
              (\i : num. if i < 2 then EL i xs else i * EL i xs)
              (count 64))} =
    FACT 2016 DIV FACT 1953 - FACT 63 * 2016``;
