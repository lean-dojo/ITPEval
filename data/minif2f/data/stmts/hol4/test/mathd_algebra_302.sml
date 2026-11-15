(*
  Statement-only formalization of miniF2F test problem mathd_algebra_302: the square of half
  the imaginary unit equals negative one quarter in the complex numbers. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open complexTheory;

val mathd_algebra_302 =
  ``(i / 2) pow 2 = ~(1 / 4 : complex)``;
