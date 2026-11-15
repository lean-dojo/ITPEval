(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a2:
  the real coefficient pairs for which every complex root of
  z^2 + b*z + c lies strictly inside the unit disk. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory complexTheory;

val putnam_1975_a2 =
  ``!b c : real.
      ((!z : complex.
          z pow 2 +
          complex_of_real b * z +
          complex_of_real c = 0
          ==>
          modu z < 1)
       <=>
       c < 1 /\
       c - b > -1 /\
       c + b > -1)``;
