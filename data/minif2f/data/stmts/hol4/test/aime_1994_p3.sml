(*
  Statement-only formalization of miniF2F test problem aime_1994_p3: an integer recurrence
  determining the remainder of f 94 modulo 1000. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val aime_1994_p3 =
  ``!f : int -> int.
      (!x : int. f x + f (x - 1) = x ** 2) /\
      f 19 = 94
      ==>
      f 94 % 1000 = 561``;
