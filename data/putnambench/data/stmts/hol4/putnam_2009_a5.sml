(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a5:
  no finite abelian group has product of the orders of all its elements equal
  to 2^2009. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory monoidTheory groupTheory;

val putnam_2009_a5 =
  ``((?g : num group.
        FiniteAbelianGroup g /\
        PROD_IMAGE (order g) g.carrier = 2 ** 2009)
     <=> F)``;
