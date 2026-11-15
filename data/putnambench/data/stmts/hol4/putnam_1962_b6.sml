(*
  Statement-only formalization of PutnamBench artifact putnam_1962_b6:
  a bounded real trigonometric polynomial attaining unit absolute value at
  2n points is, when nonconstant, a phase-shifted cosine. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;

val putnam_1962_b6 =
  ``!n : num. !a b : num -> real.
      !xs : real set. !f : real -> real.
        f =
          (\x : real.
             SIGMA
               (\k : num.
                  a k * sin (&k * x) + b k * cos (&k * x))
               (count (SUC n))) /\
        (!x : real.
           0 <= x /\ x <= 2 * pi ==> abs (f x) <= 1) /\
        FINITE xs /\
        CARD xs = 2 * n /\
        (!x : real.
           x IN xs ==> 0 <= x /\ x < 2 * pi) /\
        (!x : real.
           x IN xs ==> abs (f x) = 1)
        ==>
        (~(?c : real. f = (\x : real. c))
         ==>
         ?phase : real.
           f = (\x : real. cos (&n * x + phase)))``;
