(*
  Statement-only formalization of miniF2F test problem imo_1982_p1: a nearly
  additive natural-valued function with specified values. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val imo_1982_p1 =
  ``!f : num -> num.
      (!m n. 0 < m /\ 0 < n ==>
        (f (m + n) = f m + f n \/
         f (m + n) = f m + f n + 1)) /\
      f 2 = 0 /\
      0 < f 3 /\
      f 9999 = 3333
      ==>
      f 1982 = 660``;
