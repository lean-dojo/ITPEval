(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_15: evaluating a
  symmetric sum of natural-number powers at the inputs 2 and 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_15 =
  ``!s : num -> num -> num.
      (!a b : num.
        0 < a /\ 0 < b
        ==>
        s a b = a EXP b + b EXP a)
      ==>
      s 2 6 = 100``;
