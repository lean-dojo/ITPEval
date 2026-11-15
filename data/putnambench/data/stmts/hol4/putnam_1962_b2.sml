(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b2:
  existence of a function from the reals to subsets of the natural numbers
  that is strictly increasing under proper inclusion. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val putnam_1962_b2 =
  ``?f : real -> num set.
      !a b : real.
        a < b
        ==>
        f a PSUBSET f b``;
