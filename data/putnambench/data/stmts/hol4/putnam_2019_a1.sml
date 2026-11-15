(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2019_a1:
  the values of A^3 + B^3 + C^3 - 3ABC for nonnegative integers are exactly
  the nonnegative integers not congruent to 3 or 6 modulo 9. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory pred_setTheory;

val putnam_2019_a1 =
  ``{n : int |
       ?A B C : int.
         0 <= A /\ 0 <= B /\ 0 <= C /\
         A ** 3 + B ** 3 + C ** 3 - 3 * A * B * C = n} =
    {n : int |
       0 <= n /\ n % 9 <> 3 /\ n % 9 <> 6}``;
