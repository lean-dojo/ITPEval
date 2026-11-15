(*
  Statement-only formalization of miniF2F test problem
  algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778: a real cube-root witness
  satisfying x + 1/x = 3 determines r^3 + 1/r^3. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 =
  ``!r : real.
      (?x : real. x pow 3 = r /\ x + 1 / x = 3)
      ==>
      r pow 3 + 1 / (r pow 3) = 5778``;
