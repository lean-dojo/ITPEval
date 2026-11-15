(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b4:
  for every natural n at least two, an integer-coefficient polynomial in
  three variables recovers x from x^n, x^(n+1), and x+x^(n+2).
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory;

val putnam_1972_b4 =
  ``!n : num.
      1 < n
      ==>
      ?P : (num # num) # num -> int.
        FINITE {e | P e <> 0} /\
        !x : int.
          x =
          ITSET
            (\e acc.
               P e *
                 (x ** n) ** FST (FST e) *
                 (x ** (n + 1)) ** SND (FST e) *
                 (x + x ** (n + 2)) ** SND e +
               acc)
            {e | P e <> 0}
            0``;
