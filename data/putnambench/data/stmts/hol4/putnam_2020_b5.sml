(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_b5:
  four unit-modulus complex numbers, none equal to one, make the specified
  symmetric polynomial expression nonzero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val putnam_2020_b5 =
  ``!z1 z2 z3 z4 : complex.
      modu z1 = 1 /\
      modu z2 = 1 /\
      modu z3 = 1 /\
      modu z4 = 1 /\
      z1 <> 1 /\
      z2 <> 1 /\
      z3 <> 1 /\
      z4 <> 1
      ==>
      3 - z1 - z2 - z3 - z4 + z1 * z2 * z3 * z4 <> 0``;
