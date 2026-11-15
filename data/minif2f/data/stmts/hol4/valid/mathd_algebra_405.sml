(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_405:
  exactly the positive natural numbers 1 and 2 satisfy x^2 + 4*x + 4 < 20.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val mathd_algebra_405 =
  ``!x : num.
      (0 < x /\ x EXP 2 + 4 * x + 4 < 20)
      <=>
      x = 1 \/ x = 2``;
