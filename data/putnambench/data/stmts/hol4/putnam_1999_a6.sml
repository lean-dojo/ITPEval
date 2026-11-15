(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_a6:
  a real sequence satisfying the specified rational recurrence has every
  positive-indexed term equal to an integer multiple of its index. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1999_a6 =
  ``!a : num -> real.
      a 1 = 1 /\
      a 2 = 2 /\
      a 3 = 24 /\
      (!n : num.
         4 <= n
         ==>
         a n =
           (6 * (a (n - 1)) pow 2 * a (n - 3) -
            8 * a (n - 1) * (a (n - 2)) pow 2) /
           (a (n - 2) * a (n - 3)))
      ==>
      !n : num.
        1 <= n
        ==>
        ?k : int.
          a n = real_of_int k * (&n : real)``;
