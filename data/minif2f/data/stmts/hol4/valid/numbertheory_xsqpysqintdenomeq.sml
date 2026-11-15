(*
  Statement-only formalization of miniF2F valid problem numbertheory_xsqpysqintdenomeq:
  rational numbers whose sum of squares has reduced denominator one have equal reduced
  denominators. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory ratTheory;

val numbertheory_xsqpysqintdenomeq =
  ``!x y : rat.
      RATD (x * x + y * y) = 1
      ==>
      RATD x = RATD y``;
