(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a1:
  four distinct points on the quartic y = 2x^4 + 7x^3 + 3x - 5 that are
  collinear have average x-coordinate -7/8. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val putnam_1977_a1 =
  ``let y =
      \x : real. 2 * x pow 4 + 7 * x pow 3 + 3 * x - 5
    in
      !S : real set.
        FINITE S /\
        CARD S = 4
        ==>
        ((?m b : real.
            !x : real.
              x IN S ==> y x = m * x + b)
         ==>
         SIGMA (\x : real. x) S / 4 = -(7 : real) / 8)``;
