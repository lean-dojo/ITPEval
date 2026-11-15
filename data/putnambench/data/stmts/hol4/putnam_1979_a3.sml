(*
  Statement-only formalization of PutnamBench artifact putnam_1979_a3:
  a nonzero real sequence satisfying a rational recurrence has infinitely many
  integer-valued terms exactly when its first two values are the same integer.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory;

val putnam_1979_a3 =
  ``!x : num -> real.
      (!n : num.
         x n <> 0 /\
         (3 <= n
          ==>
          x n =
            x (n - 2) * x (n - 1) /
            (2 * x (n - 2) - x (n - 1))))
      ==>
      ((!m : num.
          ?n : num.
            m < n /\
            (?a : int. x n = real_of_int a))
       <=>
       ?k : int.
         x 1 = real_of_int k /\
         x 2 = real_of_int k)``;
