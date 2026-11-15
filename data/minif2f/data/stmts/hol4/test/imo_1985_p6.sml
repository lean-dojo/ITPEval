(*
  Statement-only formalization of miniF2F test problem imo_1985_p6: existence and uniqueness
  of a positive initial value whose recurrence is strictly increasing and remains below 1.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val imo_1985_p6 =
  ``!f : num -> real -> real.
      (!x. 0 < x ==> f 1 x = x) /\
      (!x n.
        0 < x ==>
        f (n + 1) x =
          f n x * (f n x + 1 / (&n : real)))
      ==>
      ?!a : real.
        0 < a /\
        !n.
          0 < n ==>
          0 < f n a /\
          f n a < f (n + 1) a /\
          f (n + 1) a < 1``;
