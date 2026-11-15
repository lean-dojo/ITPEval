(*
  Statement-only formalization of miniF2F test problem amc12_2001_p5: the product of the odd
  natural numbers below 10000 as a quotient of factorials. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val _ = new_theory "hello";

val amc12_2001_p5 =
  ``PROD_SET {x : num | x < 10000 /\ ODD x} =
      FACT 10000 DIV ((2 ** 5000) * FACT 5000)``;

val _ = export_theory();
