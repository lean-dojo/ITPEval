(*
  Statement-only formalization of miniF2F valid problem
  algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3: an integer identity implying
  divisibility of a sum of cubes. This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val algebra_xmysqpymzsqpzmxsqeqxyz_xpypzp6dvdx3y3z3 =
  ``!x y z : int.
      (x - y) ** 2 + (y - z) ** 2 + (z - x) ** 2 = x * y * z
      ==>
      (x + y + z + 6) int_divides
        (x ** 3 + y ** 3 + z ** 3)``;
