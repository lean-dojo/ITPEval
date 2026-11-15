(*
  Statement-only formalization of miniF2F valid problem
  algebra_2rootspoly_apatapbeq2asqp2ab: a polynomial distributive identity over the complex
  numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val _ = new_theory "hello";

val algebra_2rootspoly_apatapbeq2asqp2ab =
  ``!a b : complex.
      (a + a) * (a + b) = 2 * (a pow 2) + 2 * (a * b)``;

val _ = export_theory();
