(*
  Statement-only formalization of miniF2F test problem imo_2019_p1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val imo_2019_p1 =
  ``!f : int -> int.
      (!a b : int.
         f (2 * a) + 2 * f b = f (f (a + b))) <=>
      ((!z : int. f z = 0) \/
       (?c : int. !z : int. f z = 2 * z + c))``;
