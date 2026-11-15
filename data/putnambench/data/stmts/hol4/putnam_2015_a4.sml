(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2015_a4:
  the greatest uniform lower bound on [0,1) of the binary series indexed by
  positive integers whose multiples of x have even floor is 4/7. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory realTheory intrealTheory seqTheory;

val putnam_2015_a4 =
  ``let f =
      \x : real.
        suminf
          (\n : num.
             if 0 < n /\
                (2 : int) int_divides INT_FLOOR ((&n : real) * x)
             then 1 / (2 : real) pow n
             else 0)
    in
    let solution = (4 / 7 : real)
    in
      (!x : real.
         0 <= x /\ x < 1
         ==>
         solution <= f x) /\
      (!l : real.
         (!x : real.
            0 <= x /\ x < 1
            ==>
            l <= f x)
         ==>
         l <= solution)``;
