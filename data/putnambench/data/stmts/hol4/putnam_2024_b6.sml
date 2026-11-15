(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6:
  the threshold real exponent governing whether the exponentially normalized
  power series tends to zero or positive infinity as x approaches 1 from the
  left is -1/2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory seqTheory transcTheory;

val putnam_2024_b6 =
  ``let left_tends_to =
      \f : real -> real.
      \l : real.
        !epsilon : real.
          0 < epsilon
          ==>
          ?delta : real.
            0 < delta /\
            !x : real.
              0 < 1 - x /\ 1 - x < delta
              ==>
              abs (f x - l) < epsilon
    in
    let left_tends_to_posinfinity =
      \f : real -> real.
        !M : real.
          ?delta : real.
            0 < delta /\
            !x : real.
              0 < 1 - x /\ 1 - x < delta
              ==>
              M < f x
    in
      !F : real -> real -> real. !c : real.
        (!a x : real.
           0 <= x /\ x < 1
           ==>
           (\n : num.
              (&(n + 1) : real) powr a *
              exp (2 * (&(n + 1) : real)) *
              x pow ((n + 1) EXP 2))
             sums F a x)
        ==>
        (((!a : real.
             a < c
             ==>
             left_tends_to
               (\x : real.
                  F a x * exp (-(1 / (1 - x))))
               0) /\
          (!a : real.
             c < a
             ==>
             left_tends_to_posinfinity
               (\x : real.
                  F a x * exp (-(1 / (1 - x))))))
         <=>
         c = -(1 / 2))``;
