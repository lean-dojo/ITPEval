(*
  Statement-only formalization of miniF2F valid artifact
  algebra_manipexpr_2erprsqpesqeqnrpnesq: a polynomial identity in two complex
  numbers involving addition, multiplication, negation, and squares. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_manipexpr_2erprsqpesqeqnrpnesq =
  ``!e r : complex.
      2 * (e * r) + (e pow 2 + r pow 2) = (~r + ~e) pow 2``;
