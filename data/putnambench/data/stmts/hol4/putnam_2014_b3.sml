(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2014_b3:
  a positive-dimensional rational matrix with at least m+n distinct prime
  absolute entry values has rank at least two. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory primeTheory ratTheory;

val putnam_2014_b3 =
  ``!m n : num. !A : num -> num -> rat.
      0 < m /\
      0 < n /\
      m + n <=
        CARD
          {p : num |
             prime p /\
             ?i j : num.
               i < m /\
               j < n /\
               (A i j = rat_of_num p \/
                A i j = ~(rat_of_num p))}
      ==>
      ?i1 i2 j1 j2 : num.
        i1 < m /\
        i2 < m /\
        j1 < n /\
        j2 < n /\
        i1 <> i2 /\
        j1 <> j2 /\
        A i1 j1 * A i2 j2 - A i1 j2 * A i2 j1 <> 0q``;
