(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_67: evaluating the
  composition of two explicitly defined real functions at -1 gives 2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_67 =
  ``!f g : real -> real.
      (!x : real. f x = 5 * x + 3) /\
      (!x : real. g x = x pow 2 - 2)
      ==>
      g (f (-1)) = 2``;
