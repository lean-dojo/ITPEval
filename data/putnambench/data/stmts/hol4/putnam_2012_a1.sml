(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a1:
  among twelve real numbers in the open interval (1,12), three distinct
  entries are the side lengths of an acute triangle. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val putnam_2012_a1 =
  ``!d : num -> real.
      (!i : num. i < 12 ==> 1 < d i /\ d i < 12)
      ==>
      ?i j k : num.
        i < 12 /\
        j < 12 /\
        k < 12 /\
        i <> j /\
        i <> k /\
        j <> k /\
        d i <= d k /\
        d j <= d k /\
        d k pow 2 < d i pow 2 + d j pow 2``;
