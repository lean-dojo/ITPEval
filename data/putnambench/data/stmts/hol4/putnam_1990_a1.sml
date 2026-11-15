(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a1:
  the integer sequence with the specified third-order recurrence equals the
  sum of the factorial and power-of-two sequences. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_1990_a1 =
  ``!T : num -> int.
      T 0 = 2 /\
      T 1 = 3 /\
      T 2 = 6 /\
      (!n : num.
         T (n + 3) =
           int_of_num (n + 7) * T (n + 2) -
           4 * int_of_num (n + 3) * T (n + 1) +
           int_of_num (4 * n + 4) * T n)
      ==>
      T =
        (\n : num.
           int_of_num (FACT n) + int_of_num (2 EXP n))``;
