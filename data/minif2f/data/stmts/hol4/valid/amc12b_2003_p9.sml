(*
  Statement-only formalization of miniF2F valid problem amc12b_2003_p9: a real affine function
  whose values at 6 and 2 differ by 12 has values at 12 and 2 differing by 30. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val _ = new_theory "hello";

val amc12b_2003_p9 =
  ``!a b : real. !f : real -> real.
      (!x : real. f x = a * x + b) /\
      f 6 - f 2 = 12
      ==>
      f 12 - f 2 = 30``;

val _ = export_theory();
