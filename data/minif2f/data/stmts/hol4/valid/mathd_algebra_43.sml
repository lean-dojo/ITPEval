(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_43: a real affine function
  with values 4 at 7 and 3 at 6 has value 0 at 3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val mathd_algebra_43 =
  ``!a b : real. !f : real -> real.
      (!x : real. f x = a * x + b) /\
      f 7 = 4 /\
      f 6 = 3
      ==>
      f 3 = 0``;
