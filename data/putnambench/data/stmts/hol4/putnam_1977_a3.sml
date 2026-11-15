(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a3:
  the explicit recovery of a real-valued function from two symmetric
  averages at offsets one and four. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_1977_a3 =
  ``!f g h : real -> real.
      (!x : real.
         f x = (h (x + 1) + h (x - 1)) / 2) /\
      (!x : real.
         g x = (h (x + 4) + h (x - 4)) / 2)
      ==>
      h =
        (\x : real.
           g x - f (x - 3) + f (x - 1) + f (x + 1) - f (x + 3))``;
