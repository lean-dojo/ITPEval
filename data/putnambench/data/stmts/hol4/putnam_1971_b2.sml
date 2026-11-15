(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b2:
  classification of real functions on the reals excluding zero and one that
  satisfy a functional equation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory;

val putnam_1971_b2 =
  ``let S = {x : real | x <> 0 /\ x <> 1}
    in
    let solution =
      \x : real.
        (x pow 3 - x pow 2 - 1) / (2 * x * (x - 1))
    in
    let solutions = {solution}
    in
    let P =
      \F : real -> real.
        !x : real.
          x IN S ==> F x + F ((x - 1) / x) = 1 + x
    in
      (!F : real -> real. F IN solutions ==> P F) /\
      (!f : real -> real.
         P f
         ==>
         ?F : real -> real.
           F IN solutions /\
           !x : real. x IN S ==> f x = F x)``;
