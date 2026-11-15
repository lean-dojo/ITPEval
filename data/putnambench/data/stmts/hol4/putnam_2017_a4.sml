(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2017_a4:
  quiz scores covering every integer from 0 through 10 with average 7.4 admit
  a partition into two equal-sized groups, each with average 7.4. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_2017_a4 =
  ``!N : num. !score : num -> num.
      (!i : num.
         i IN count (2 * N)
         ==>
         score i <= 10) /\
      (!k : num.
         k <= 10
         ==>
         ?i : num.
           i IN count (2 * N) /\
           score i = k) /\
      SIGMA
        (\i : num. &(score i))
        (count (2 * N)) /
        (&(2 * N) : real) =
        (74 : real) / 10
      ==>
      ?s : num set.
        s SUBSET count (2 * N) /\
        CARD s = N /\
        SIGMA
          (\i : num. &(score i))
          s /
          (&N : real) =
          (74 : real) / 10 /\
        SIGMA
          (\i : num. &(score i))
          (count (2 * N) DIFF s) /
          (&N : real) =
          (74 : real) / 10``;
