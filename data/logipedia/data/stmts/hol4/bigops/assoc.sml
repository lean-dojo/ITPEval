(*
  Statement-only formalization of the Logipedia artifact bigops.assoc:
  associativity of multiplication on natural numbers. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val bigops_assoc =
  ``!a : num.
      !b : num.
        !c : num.
          a * (b * c) = (a * b) * c``;
