(*
  Statement-only formalization of PutnamBench artifact putnam_1969_a2:
  the determinant of the real n by n matrix with entries |i - j| has the
  stated closed form for every positive n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory rich_listTheory sortingTheory;
open pred_setTheory realTheory real_sigmaTheory;

val putnam_1969_a2 =
  ``!n : num.
      0 < n
      ==>
      SIGMA
        (\p : num list.
           (-1 : real) pow
             CARD
               {ij : num # num |
                  FST ij < SND ij /\
                  SND ij < n /\
                  EL (SND ij) p < EL (FST ij) p} *
           REAL_PROD_IMAGE
             (\i : num. abs (&i - &(EL i p)))
             (count n))
        {p : num list | PERM p (GENLIST I n)} =
      (-1 : real) pow (n - 1) * &(n - 1) * 2 pow (n - 2)``;
