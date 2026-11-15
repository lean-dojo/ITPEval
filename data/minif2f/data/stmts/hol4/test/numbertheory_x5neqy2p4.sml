(*
  Statement-only formalization of miniF2F test problem numbertheory_x5neqy2p4:
  no fifth power of an integer equals the square of an integer plus 4.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val numbertheory_x5neqy2p4 =
  ``!x y : int.
      x ** 5 <> y ** 2 + 4``;
