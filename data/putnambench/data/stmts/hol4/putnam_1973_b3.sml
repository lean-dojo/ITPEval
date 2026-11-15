(*
  Statement-only formalization of PutnamBench artifact putnam_1973_b3:
  a prime-valued quadratic condition determines a unique reduced integer
  binary quadratic form of discriminant 1 - 4p. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory integerTheory pairTheory;

val putnam_1973_b3 =
  ``!p : num.
      1 < p /\
      (!x : num. x < p ==> prime (x EXP 2 - x + p))
      ==>
      ?!triple : int # int # int.
        let a = FST triple in
        let b = FST (SND triple) in
        let c = SND (SND triple) in
          b ** 2 - 4 * a * c = 1 - 4 * int_of_num p /\
          0 < a /\
          a <= c /\
          -a <= b /\
          b < a``;
