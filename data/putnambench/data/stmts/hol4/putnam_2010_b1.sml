(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2010_b1:
  the nonexistence of an infinite real sequence whose convergent m-th power
  series sums to m for every positive natural number m. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory seqTheory;

val putnam_2010_b1 =
  ``((?a : num -> real.
        !m : num.
          0 < m
          ==>
          (\i : num. a i pow m) sums (&m : real))
     <=> F)``;
