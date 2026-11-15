(*
  Statement-only formalization of miniF2F valid problem algebra_manipexpr_apbeq2cceqiacpbceqm2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_manipexpr_apbeq2cceqiacpbceqm2 =
  ``!a b c : complex.
      (a + b = 2 * c) /\
      (c = i)
      ==>
      (a * c + b * c = -2)``;
