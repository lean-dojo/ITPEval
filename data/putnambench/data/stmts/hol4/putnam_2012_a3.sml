(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a3:
  the unique continuous solution of a functional equation on [-1, 1], with
  normalization and a finite left limit at 1, is sqrt (1 - x^2). This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory real_topologyTheory transcTheory;

val putnam_2012_a3 =
  ``let S = {x : real | -1 <= x /\ x <= 1}
    in
    let solution = \x : real. sqrt (1 - x pow 2)
    in
    let satisfies =
      \f : real -> real.
        f continuous_on S /\
        (!x : real.
           x IN S
           ==>
           f x =
             ((2 - x pow 2) / 2) *
             f (x pow 2 / (2 - x pow 2))) /\
        f 0 = 1 /\
        ?y : real.
          ((\x : real. f x / sqrt (1 - x)) --> y)
            (at 1 within {x : real | x < 1})
    in
      satisfies solution /\
      !f : real -> real.
        satisfies f
        ==>
        !x : real. x IN S ==> f x = solution x``;
