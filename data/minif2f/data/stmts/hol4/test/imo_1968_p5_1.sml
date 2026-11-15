(*
  Statement-only formalization of miniF2F test artifact imo_1968_p5_1: a
  positive-step real functional recurrence involving the source-totalized
  square root implies that the function has a positive period. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val imo_1968_p5_1 =
  ``!a : real. !f : real -> real.
      0 < a /\
      (!x : real.
         f (x + a) =
           1 / 2 +
           (if 0 <= f x - (f x) pow 2
            then sqrt (f x - (f x) pow 2)
            else 0))
      ==>
      ?b : real. 0 < b /\ !x : real. f (x + b) = f x``;

val _ = export_theory();
