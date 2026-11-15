(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b4:
  evaluation of the real eighth root of the positive fixed point of the
  given continued fraction as (3 + sqrt 5) / 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory transcTheory;

val putnam_1995_b4 =
  ``let solution = ((((3 : int), 1), 5), 2)
    in
    let a = FST (FST (FST solution))
    in
    let b = SND (FST (FST solution))
    in
    let c = SND (FST solution)
    in
    let d = SND solution
    in
      !contfrac : real.
        contfrac = 2207 - 1 / contfrac /\
        1 < contfrac
        ==>
        contfrac powr (1 / 8) =
          (real_of_int a + real_of_int b * sqrt (real_of_int c)) /
          real_of_int d``;
