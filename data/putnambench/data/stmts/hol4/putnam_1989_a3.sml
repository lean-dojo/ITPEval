(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a3:
  every complex root of the specified degree-ten polynomial has modulus one.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val putnam_1989_a3 =
  ``!z : complex.
      11 * z pow 10 + 10 * i * z pow 9 + 10 * i * z - 11 = 0
      ==>
      modu z = 1``;
