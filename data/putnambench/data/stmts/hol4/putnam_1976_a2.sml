(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a2:
  for every positive integer exponent, either the corresponding difference
  or sum of powers is an integer-coefficient polynomial in
  x^2*y + x*y^2 and x^2 + x*y + y^2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory;

val putnam_1976_a2 =
  ``!n : num.
      0 < n
      ==>
      ?a : num # num -> int.
        FINITE {e | a e <> 0} /\
        ((!x y : int.
            (x + y) ** n - x ** n - y ** n =
            ITSET
              (\e acc.
                 a e *
                   (x ** 2 * y + x * y ** 2) ** FST e *
                   (x ** 2 + x * y + y ** 2) ** SND e +
                 acc)
              {e | a e <> 0}
              0) \/
         (!x y : int.
            (x + y) ** n + x ** n + y ** n =
            ITSET
              (\e acc.
                 a e *
                   (x ** 2 * y + x * y ** 2) ** FST e *
                   (x ** 2 + x * y + y ** 2) ** SND e +
                 acc)
              {e | a e <> 0}
              0))``;
