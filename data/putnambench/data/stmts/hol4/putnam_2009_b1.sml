(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_b1:
  every positive rational number is a quotient of finite products of
  factorials of primes, with repetition allowed. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory ratTheory;

val putnam_2009_b1 =
  ``let factorial_product =
      \ps : num list.
        FOLDL
          (\acc : rat. \p : num. acc * rat_of_num (FACT p))
          1q
          ps
    in
      !q : rat.
        0q < q
        ==>
        ?numerator denominator : num list.
          EVERY prime (numerator ++ denominator) /\
          q =
            factorial_product numerator /
            factorial_product denominator``;
