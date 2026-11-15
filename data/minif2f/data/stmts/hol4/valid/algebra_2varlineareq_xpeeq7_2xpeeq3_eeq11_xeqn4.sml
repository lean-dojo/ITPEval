(*
  Statement-only formalization of miniF2F valid problem
  algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4: a two-variable linear system over the
  complex numbers with its exact solution. This file contains no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val algebra_2varlineareq_xpeeq7_2xpeeq3_eeq11_xeqn4 =
  ``!x e : complex.
      (x + e = 7) /\
      (2 * x + e = 3)
      ==>
      (e = 11) /\ (x = -4)``;
