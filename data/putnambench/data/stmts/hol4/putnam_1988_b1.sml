(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1988_b1:
  every product of two integers at least two is representable as
  x*y + x*z + y*z + 1 for positive integers x, y, and z. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val putnam_1988_b1 =
  ``!a : int.
      2 <= a
      ==>
      !b : int.
        2 <= b
        ==>
        ?x y z : int.
          0 < x /\
          0 < y /\
          0 < z /\
          a * b = x * y + x * z + y * z + 1``;
