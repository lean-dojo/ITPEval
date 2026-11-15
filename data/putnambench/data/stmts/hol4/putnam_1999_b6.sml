(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b6:
  a finite set of integers greater than one satisfying a universal gcd
  dichotomy contains two elements whose gcd is prime. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory gcdTheory integerTheory pred_setTheory;

val putnam_1999_b6 =
  ``!S : int set.
      FINITE S /\
      (!s : int. s IN S ==> 1 < s) /\
      (!n : int.
         ?s : int.
           s IN S /\
           (gcd (Num (ABS s)) (Num (ABS n)) = 1 \/
            gcd (Num (ABS s)) (Num (ABS n)) = Num (ABS s)))
      ==>
      ?s t : int.
        s IN S /\
        t IN S /\
        prime (gcd (Num (ABS s)) (Num (ABS t)))``;
