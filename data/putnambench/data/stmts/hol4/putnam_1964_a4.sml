(*
  Statement-only formalization of PutnamBench artifact putnam_1964_a4:
  every bounded integer sequence satisfying the given fourth-order rational
  recurrence with nonzero denominators is eventually periodic. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1964_a4 =
  ``!u : num -> int.
      (?B T : int.
         !n : num. B <= u n /\ u n <= T) /\
      (!n : num.
         4 <= n
         ==>
         real_of_int (u n) =
           (real_of_int (u (n - 1)) +
            real_of_int (u (n - 2)) +
            real_of_int (u (n - 3)) * real_of_int (u (n - 4))) /
           (real_of_int (u (n - 1)) * real_of_int (u (n - 2)) +
            real_of_int (u (n - 3)) +
            real_of_int (u (n - 4))) /\
         (real_of_int (u (n - 1)) * real_of_int (u (n - 2)) +
          real_of_int (u (n - 3)) +
          real_of_int (u (n - 4))) <> 0)
      ==>
      ?N c : num.
        0 < c /\
        !n : num. N <= n ==> u (n + c) = u n``;
