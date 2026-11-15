(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2002_a5:
  a recursively defined rational sequence has every positive rational as a
  ratio of consecutive terms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val putnam_2002_a5 =
  ``!a : num -> rat.
      a 0 = 1q /\
      (!n : num.
         a (2 * n + 1) = a n /\
         a (2 * n + 2) = a n + a (n + 1))
      ==>
      !q : rat.
        0q < q
        ==>
        ?n : num.
          1 <= n /\
          q = a (n - 1) / a n``;
