(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a4:
  a globally differentiable real function with globally differentiable first
  derivative has derivative bounded by two on a sufficiently long interval
  when the function and its second derivative are bounded by one there. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory;

val putnam_1962_a4 =
  ``!f : real -> real. !a b : real.
      (!x : real. higher_differentiable 2 f x) /\
      (!x : real.
         a <= x /\ x <= b
         ==>
         abs (f x) <= 1) /\
      (!x : real.
         a <= x /\ x <= b
         ==>
         abs (diffn 2 f x) <= 1) /\
      2 <= b - a
      ==>
      !x : real.
        a <= x /\ x <= b
        ==>
        abs (diffn 1 f x) <= 2``;
