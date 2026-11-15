(*
  Statement-only formalization of miniF2F valid problem amc12a_2009_p9: a real quadratic
  polynomial specified by a shifted identity has coefficient sum 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val _ = new_theory "hello";

val amc12a_2009_p9 =
  ``!a b c : real. !f : real -> real.
      (!x : real.
         f (x + 3) = 3 * x pow 2 + 7 * x + 4) /\
      (!x : real.
         f x = a * x pow 2 + b * x + c)
      ==>
      a + b + c = 2``;

val _ = export_theory();
