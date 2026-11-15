(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a6:
  exact powers of two dividing a difference of terms in a recursively defined
  integer sequence. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory;

val putnam_2025_a6 =
  ``!b : num -> int.
      b 0 = 0 /\
      (!n : num.
         b (n + 1) = 2 * b n ** 2 + b n + 1)
      ==>
      !k : num.
        1 <= k
        ==>
        ((2 : int) ** (2 * k + 2)) int_divides
          (b (2 EXP (k + 1)) - 2 * b (2 EXP k)) /\
        ~(((2 : int) ** (2 * k + 3)) int_divides
          (b (2 EXP (k + 1)) - 2 * b (2 EXP k)))``;
