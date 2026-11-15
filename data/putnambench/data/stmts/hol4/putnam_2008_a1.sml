(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a1:
  every real-valued function of two real variables whose cyclic sum vanishes
  is the difference of the values of a real-valued potential function. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val putnam_2008_a1 =
  ``!f : real -> real -> real.
      (!x y z : real. f x y + f y z + f z x = 0)
      ==>
      ?g : real -> real.
        !x y : real. f x y = g x - g y``;
