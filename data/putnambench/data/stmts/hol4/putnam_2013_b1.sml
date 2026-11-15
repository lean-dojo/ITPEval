(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_b1:
  the value of a finite correlation sum for the integer sequence determined
  recursively by its values at even and odd positive indices. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_2013_b1 =
  ``!c : num -> int.
      c 1 = 1 /\
      (!n : num.
         0 < n
         ==>
         c (2 * n) = c n) /\
      (!n : num.
         0 < n
         ==>
         c (2 * n + 1) = (-1 : int) ** n * c n)
      ==>
      SIGMA
        (\n : num. c n * c (n + 2))
        (IMAGE SUC (count 2013)) =
      -1``;
