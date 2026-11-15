(*
  Statement-only formalization of miniF2F test problem numbertheory_4x3m7y3neq2003:
  no integers x and y make 4 times x cubed minus 7 times y cubed equal 2003.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val numbertheory_4x3m7y3neq2003 =
  ``!x y : int.
      4 * x ** 3 - 7 * y ** 3 <> 2003``;
